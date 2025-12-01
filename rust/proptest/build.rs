fn main() {
    // Declare valid cfg options to avoid warnings
    println!("cargo:rustc-check-cfg=cfg(buf_size_20)");
    println!("cargo:rustc-check-cfg=cfg(buf_size_50)");
    println!("cargo:rustc-check-cfg=cfg(buf_size_100)");
    println!("cargo:rustc-check-cfg=cfg(proptest_500)");
    println!("cargo:rustc-check-cfg=cfg(proptest_1000)");
    println!("cargo:rustc-check-cfg=cfg(proptest_10000)");
    
    // Allow overriding BUF_SIZE via environment variable
    if let Ok(size) = std::env::var("BUF_SIZE") {
        println!("cargo:rustc-cfg=buf_size_{}", size);
        println!("cargo:rerun-if-env-changed=BUF_SIZE");
    }
    
    // Allow overriding PROPTEST_CASES via environment variable  
    if let Ok(cases) = std::env::var("PROPTEST_CASES") {
        println!("cargo:rustc-cfg=proptest_{}", cases);
        println!("cargo:rerun-if-env-changed=PROPTEST_CASES");
    }
}
