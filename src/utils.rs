#[macro_export]
macro_rules! trace {
    ($location:expr, $($arg:tt)*) => {
        if cfg!(debug_assertions) {
            println!("{:>8} TRACE: {}", $location, format_args!($($arg)*))
        }
    };
}