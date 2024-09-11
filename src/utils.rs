#[macro_export]
macro_rules! trace {
    ($location:expr, $($arg:tt)*) => {
        println!("{:>8} TRACE: {}", $location, format_args!($($arg)*))
    };
}