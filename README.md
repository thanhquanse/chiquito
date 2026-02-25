# ZKP Chiquito

**Chiquito** is a high-level, structured domain-specific language (DSL) for implementing zero-knowledge proof (ZKP) applications. This is a redesigned fork of [privacy-scaling-explorations/chiquito](https://github.com/privacy-scaling-explorations/chiquito), optimized for ZKP workflows including range checks, parameter generation, proof generation, and verification, etc.

## Features

- High-level ZKP circuit design
- Integrated range checking primitives
- Streamlined proof generation and verification
- Plonkish backend with compatibility bug fixes
- Python-Rust interoperability via PyO3

## Prerequisites

### Rust
- **Version**: 1.83 or higher
- **Install**: [rust-lang.org/tools/install](https://www.rust-lang.org/tools/install)
- **Verify**: `rustc --version`

### Python
- **Version**: 3.10 or higher
- **Install**: [python.org/downloads](https://www.python.org/downloads/)

### PyO3 & Maturin
- [PyO3 Documentation](https://pyo3.rs/v0.28.2/index.html)
- [Maturin Installation](https://www.maturin.rs/installation.html)

## Quick Start

1. **Clone the repository**:
   ```bash
   wget -O zkpchiquito.zip https://anonymous.4open.science/api/repo/chiquito-9B54/zip
   unzip zkpchiquito.zip -d ./path/to/zkpchiquito
   cd ./path/to/zkpchiquito```

2. **Set up Python virtual environment**:
    ```bash
    python -m venv .venv
    source .venv/bin/activate  # On Windows: .venv\Scripts\activate

3. **Install dependencies**:
    ```bash
    pip install -r requirements.txt
    maturin develop

## Backend Requirements
This framework uses a customized Plonkish backend defined in Cargo.toml. The backend includes bug fixes. If using alternative backends, ensure compatibility.

## Troubleshooting
If you encounter type annotation errors during build, edit the file for the error lines:
```bash 
vi ~/.cargo/git/checkouts/zkp-sparql-plonkish-xxx/plonkish_backend/src/backend/hyperplonk/util.rs
```

## Documentation
For detailed usage, refer to the original: [Chiquito documentation](https://github.com/privacy-scaling-explorations/chiquito).
