// NOTE
// std::intrinsics::assume is unstable at this time.
macro_rules! assume {
    ($cond:expr) => {
        if !$cond {
            if cfg!(debug_assertions) {
                unreachable!();
            } else {
                unsafe {
                    std::hint::unreachable_unchecked();
                }
            }
        };
    };
}

// NOTE
// std::intrinsics::unlikely is unstable at this time.
macro_rules! unlikely {
    ($cond:expr) => {
        $cond
    };
}
