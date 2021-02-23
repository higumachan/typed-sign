use num::Signed;
use std::convert::TryFrom;
use std::ops::{Add, Sub};
use std::result::Result;

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

macro_rules! zero_operators {
    ($self_type: ident) => {
        impl<S: Signed + Copy + Add> Add<Zero> for $self_type<S> {
            type Output = $self_type<S>;

            fn add(self, rhs: Zero) -> Self::Output {
                self
            }
        }
        impl<S: Signed + Copy + Add> Sub<Zero> for $self_type<S> {
            type Output = $self_type<S>;

            fn sub(self, rhs: Zero) -> Self::Output {
                self
            }
        }
    };
}

macro_rules! add_operator {
    ($self_type: ident) => {
        add_operator!($self_type, $self_type, $self_type<S>, from_value_unchecked);
    };
    ($self_type: ident, $other_type: ident) => {
        add_operator!($self_type, $other_type, $self_type<S>, from_value_unchecked);
    };
    ($self_type: ident, $other_type: ident, $output_type: ty) => {
        add_operator!($self_type, $other_type, $output_type, from_value);
    };
    ($self_type: ident, $other_type: ident, $output_type: ty, $from_value_function: ident) => {
        impl<S: Signed + Copy + Add> Add<$other_type<S>> for $self_type<S> {
            type Output = $output_type;

            fn add(self, rhs: $other_type<S>) -> Self::Output {
                Self::$from_value_function(self.value().add(rhs.value()))
            }
        }
    };
}

macro_rules! sub_operator {
    ($self_type: ident, $other_type: ident, $from_value_function: ident) => {
        impl<S: Signed + Copy + Sub> Sub<$other_type<S>> for $self_type<S> {
            type Output = output_type;

            fn sub(self, rhs: $other_type<S>) -> Self::Output {
                Self::$from_value_function(self.value().sub(rhs.value()))
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

pub trait AsValue<S: Copy + Signed + Sized> {
    fn value(&self) -> S;
}

#[derive(Copy, Clone)]
pub struct Positive<S: Signed + Copy>(S);

impl_value!(Positive);

pub trait FromValue<S: Copy>
where
    Self: Sized,
{
    type Other: FromValue<S>;

    fn from_value(value: S) -> Result<Self, Self::Other>;

    fn from_value_unchecked(value: S) -> Self;
}

impl<S: Signed + Copy + Sized> FromValue<S> for Positive<S> {
    type Other = NonPositive<S>;

    fn from_value(value: S) -> Result<Self, Self::Other> {
        value
            .is_positive()
            .then(|| Self(value))
            .ok_or_else(|| NonPositive::from_value_unchecked(value))
    }

    fn from_value_unchecked(value: S) -> Self {
        Self(value)
    }
}

//add_sub_operator!(Positive, Negative, NonNegative, NonPositive);
zero_operators!(Positive);
add_operator!(Positive);
add_operator!(Positive, NonNegative);
add_operator!(Positive, Negative, Result<Positive<S>, NonPositive<S>>);
add_operator!(Positive, NonPositive, Result<Positive<S>, NonPositive<S>>);

#[derive(Copy, Clone)]
pub struct Negative<S: Signed>(S);

impl_value!(Negative);

impl<S: Signed + Copy + Sized> FromValue<S> for Negative<S> {
    type Other = NonNegative<S>;

    fn from_value(value: S) -> Result<Self, Self::Other> {
        value
            .is_negative()
            .then(|| Self(value))
            .ok_or_else(|| Self::Other::from_value_unchecked(value))
    }

    fn from_value_unchecked(value: S) -> Self {
        Self(value)
    }
}

zero_operators!(Negative);
add_operator!(Negative, Positive, Result<Negative<S>, NonNegative<S>>);
add_operator!(Negative, NonNegative, Result<Negative<S>, NonNegative<S>>);
add_operator!(Negative);
add_operator!(Negative, NonPositive);

#[derive(Copy, Clone)]
pub struct Zero {}

#[derive(Copy, Clone)]
pub enum NonNegative<S: Copy + Signed> {
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
        } else if value.is_positive() {
            Ok(Self::Positive(Positive::from_value_unchecked(value)))
        } else {
            Err(Negative::from_value_unchecked(value))
        }
    }

    fn from_value_unchecked(value: S) -> Self {
        if value.is_zero() {
            Self::Zero
        } else {
            Self::Positive(Positive::from_value_unchecked(value))
        }
    }
}

zero_operators!(NonNegative);
add_operator!(NonNegative, Positive);
add_operator!(NonNegative);
add_operator!(NonNegative, Negative, Result<NonNegative<S>, Negative<S>>);
add_operator!(
    NonNegative,
    NonPositive,
    Result<NonNegative<S>, Negative<S>>
);

macro_rules! non_some_one_impls {
    ($self: ident, $self_inner: ident, $self_inner_lower: ident) => {
        impl<S: Copy + Signed> $self<S> {
            pub fn zero(&self) -> Result<Zero, $self_inner<S>> {
                match self {
                    Self::Zero => Ok(Zero {}),
                    Self::$self_inner(p) => Err(*p),
                }
            }
            pub fn $self_inner_lower(&self) -> Result<$self_inner<S>, Zero> {
                match self {
                    Self::Zero => Err(Zero {}),
                    Self::$self_inner(p) => Ok(*p),
                }
            }
        }
    };
}

non_some_one_impls!(NonNegative, Positive, positive);

#[derive(Copy, Clone)]
pub enum NonPositive<S: Copy + Signed + Sized> {
    Zero,
    Negative(Negative<S>),
}

impl<S: Copy + Signed + Sized> AsValue<S> for NonPositive<S> {
    fn value(&self) -> S {
        self.negative().map(|x| x.value()).unwrap_or(S::zero())
    }
}

impl<S: Copy + Signed + Sized> FromValue<S> for NonPositive<S> {
    type Other = Positive<S>;

    fn from_value(value: S) -> Result<Self, Self::Other> {
        if value.is_zero() {
            Ok(Self::Zero)
        } else if value.is_negative() {
            Ok(Self::Negative(Negative::from_value_unchecked(value)))
        } else {
            Err(Positive::from_value_unchecked(value))
        }
    }

    fn from_value_unchecked(value: S) -> Self {
        if value.is_zero() {
            Self::Zero
        } else {
            Self::Negative(Negative::from_value_unchecked(value))
        }
    }
}

zero_operators!(NonPositive);
add_operator!(NonPositive, Positive, Result<NonPositive<S>, Positive<S>>);
add_operator!(
    NonPositive,
    NonNegative,
    Result<NonPositive<S>, Positive<S>>
);
add_operator!(NonPositive, Negative);
add_operator!(NonPositive);

non_some_one_impls!(NonPositive, Negative, negative);

#[cfg(test)]
mod tests {
    use crate::Negative;
    use crate::Positive;

    #[test]
    fn it_works() {
        let p1 = Positive(1.0);
        let p2 = Positive(3.0);
        let p3 = p1 + p2;
        let n1 = Negative(2.0);
        let e1 = p1 + n1;
    }
}
