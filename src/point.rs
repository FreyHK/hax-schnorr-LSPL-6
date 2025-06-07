//! Defines affine coordinate points

#[derive(Debug)]
pub enum Point<N> {
    Infinity,
    Affine(N, N),
}

impl<N: PartialEq> PartialEq for Point<N> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Point::Infinity, Point::Infinity) => true,
            (Point::Affine(x1, y1), Point::Affine(x2, y2)) => x1 == x2 && y1 == y2,
            _ => false,
        }
    }
    
    fn ne(&self, other: &Self) -> bool {
        !match (self, other) {
            (Point::Infinity, Point::Infinity) => true,
            (Point::Affine(x1, y1), Point::Affine(x2, y2)) => x1 == x2 && y1 == y2,
            _ => false,
        }
    }
}

impl<N: Clone> Clone for Point<N> {
    fn clone(&self) -> Self {
        match self {
            Self::Infinity => Self::Infinity,
            Self::Affine(x, y) => Self::Affine(x.clone(), y.clone()),
        }
    }
}