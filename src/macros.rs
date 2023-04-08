#[macro_export]
macro_rules! assume {
    ($cond:expr) => {
        if cfg!(debug_assertions) {
            debug_assert!($cond);
        } else if !$cond {
            unsafe {
                std::hint::unreachable_unchecked();
            }
        }
    };
}

// TODO
// Use std::intrinsics::unlikeyly.
#[macro_export]
macro_rules! unlikely {
    ($cond:expr) => {
        $cond
    };
}
