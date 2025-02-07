#[macro_export]
macro_rules! apply_to_slices {
    ($f:expr, $len: expr, $($slice:expr),*) => {
        for i in 0..$len {
            $f($(&mut $slice[i] ),*);
        }
    };
}

#[macro_export]
macro_rules! apply_to_clauses {
    ($f:expr, $len: expr, $($clauses:expr),*) => {

        apply_to_slices!($f, $len, $($clauses.content_pos_mut()),*);
        apply_to_slices!($f, $len, $($clauses.content_neg_mut()),*);
    };
}
