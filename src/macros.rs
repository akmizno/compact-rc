// NOTE
// std::intrinsics::assume is unstable at this time.
macro_rules! assume {
    ($cond:expr) => {
        if !$cond {
            if cfg!(debug_assertions) {
                unreachable!();
            } else {
                #[allow(unused_unsafe)]
                unsafe {
                    std::hint::unreachable_unchecked();
                }
            }
        };
    };
}
