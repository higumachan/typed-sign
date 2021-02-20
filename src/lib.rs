use num::Signed;
use std::convert::TryFrom;
use std::ops::{Add, Sub};

macro_rules! impl_value {
    ($self: ident) => {
        impl<S: Copy + Signed + Sized> AsValue<S> for $self<S> {
            fn value(&self) -> S {
                self.0
            }
        }
    };
}

macro_rules! zero_operator {
    ($st: ident, $Ops: ident, $ops: ident) => {
        impl<S: Signed + Copy + $Ops> $Ops<Zero> for $st<S> {
            type Output = Self;

            fn $ops(self, _: Zero) -> Self::Output {
                self
            }
        }
    };
}

macro_rules! add_sub_operator {
    ($positive_type: ident, $negative_type: ident, $non_negative_type: ident, $non_positive_type: ident) => {
        zero_operator!($positive_type, Add, add);
        zero_operator!($positive_type, Sub, sub);

        impl<S: Signed + Copy + Add> Add for $positive_type<S> {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                Self::from_value_unchecked(self.value().add(rhs.value()))
            }
        }

        impl<S: Signed + Copy + Sub> Sub for $positive_type<S> {
            type Output = Result<Self, $non_positive_type<S>>;

            fn sub(self, rhs: Self) -> Self::Output {
                let result = self.value().sub(rhs.value());
                Self::from_value(result)
            }
        }

        impl<S: Signed + Copy + Add> Add<$negative_type<S>> for $positive_type<S> {
            type Output = Result<Self, $non_positive_type<S>>;

            fn add(self, rhs: $negative_type<S>) -> Self::Output {
                let result = self.0.add(rhs.0);
                Self::from_value(result)
            }
        }

        impl<S: Signed + Copy + Sub> Sub<$negative_type<S>> for $positive_type<S> {
            type Output = Self;

            fn sub(self, rhs: $negative_type<S>) -> Self::Output {
                Self::from_value_unchecked(self.0.sub(rhs.0))
            }
        }
    };
}

pub enum Sign {
    Positive,
    Zero,
    Negative,
}

impl<S: Signed> From<S> for Sign {
    fn from(value: S) -> Self {
        if value.is_zero() {
            Self::Zero
        } else if value.is_positive() {
            Self::Positive
        } else {
            Self::Negative
        }
    }
}

trait AsValue<S: Copy + Signed + Sized> {
    fn value(&self) -> S;
}

#[derive(Copy, Clone)]
struct Positive<S: Signed + Copy>(S);

impl_value!(Positive);

trait FromValue<S: Copy>
where
    Self: Sized,
{
    type Other: FromValue<S>;

    fn from_value(value: S) -> Result<Self, Self::Other>;

    fn from_value_unchecked(value: S) -> Self {
        Self::from_value(value).unwrap()
    }
}

impl<S: Signed + Copy + Sized> FromValue<S> for Positive<S> {
    type Other = NonPositive<S>;

    fn from_value(value: S) -> Result<Self, Self::Other> {
        value
            .is_positive()
            .then(|| Self(value))
            .ok_or_else(|| NonPositive::new_unchecked(value))
    }

    fn from_value_unchecked(value: S) -> Self {
        Self(value)
    }
}

add_sub_operator!(Positive, Negative, NonNegative, NonPositive);

#[derive(Copy, Clone)]
struct Negative<S: Signed>(S);

impl_value!(Negative);

impl<S: Signed + Copy + Sized> FromValue<S> for Negative<S> {
    type Other = NonNegative<S>;

    fn from_value(value: S) -> Result<Self, Self::Other> {
        value
            .is_negative()
            .then(|| Self(value))
            .ok_or_else(|| Self::Other::new_unchecked(value))
    }

    fn from_value_unchecked(value: S) -> Self {
        Self(value)
    }
}

add_sub_operator!(Negative, Positive, NonPositive, NonNegative);

#[derive(Copy, Clone)]
struct Zero {}

impl Zero {
    fn value() {}
}

#[derive(Copy, Clone)]
enum NonNegative<S: Copy + Signed> {
    Zero,
    Positive(Positive<S>),
}

impl<S: Copy + Signed + Sized> AsValue<S> for NonNegative<S> {
    fn value(&self) -> S {
        self.positive().map(|x| x.value()).unwrap_or(S::zero())
    }
}

impl<S: Copy + Signed + Sized> FromValue<S> for NonNegative<S> {
    type Other = Negative<S>;

    fn from_value(value: S) -> Result<Self, Self::Other> {
        if value.is_zero() {
            Ok(Self::Zero)
        } else {
            Positive::from_value(value)
                .map(|x| Self::from_value_unchecked(x.0))
                .map_err(|x| x.negative().unwrap())
        }
    }
}

add_sub_operator!(NonNegative, Negative, NonNegative, NonPositive);

macro_rules! non_some_one_impls {
    ($self: ident, $self_inner: ident, $self_inner_lower: ident, $other: ident) => {
        impl<S: Copy + Signed> $self<S> {
            pub fn zero(&self) -> Result<Zero, $other<S>> {
                match self {
                    Self::Zero(z) => Ok(*z),
                    Self::$self_inner(p) => Err(*p),
                }
            }
            pub fn $self_inner_lower(&self) -> Result<$self_inner<S>, Zero> {
                match self {
                    Self::Zero(z) => Err(*z),
                    Self::$self_inner(p) => Ok(*p),
                }
            }
        }
    };
}

non_some_one_impls!(NonNegative, Positive, positive, Negative);

#[derive(Copy, Clone)]
enum NonPositive<S: Copy + Signed> {
    Zero,
    Negative(Negative<S>),
}

impl<S: Copy + Signed + Sized> FromValue<S> for NonPositive<S> {
    type Other = Positive<S>;

    fn from_value(value: S) -> Result<Self, Self::Other> {
        if value.is_zero() {
            Ok(Self::Zero)
        } else {
            Negative::from_value(value)
                .map(|x| Self::from_value_unchecked(x.0))
                .map_err(|x| x.negative().unwrap())
        }
    }
}

non_some_one_impls!(NonPositive, Negative, negative, Positive);

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
