#[macro_export]
macro_rules! trace {
    ($($arg:tt)*) => {
        if cfg!(debug_assertions) {
            println!("TRACE: {}", format_args!($($arg)*))
        }
    };
}