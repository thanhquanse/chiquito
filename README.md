# ZKP Chiquito

Chiquito is a high-level structured language for implementing zero knowledge proof (ZKP) applications. This is a re-designed version, derived from [chiquito](https://github.com/privacy-scaling-explorations/chiquito) tailored to ZKP, including the range check, parameter generation, proof generation and verification, etc.

Follow the instructions and information at [chiquito](https://github.com/privacy-scaling-explorations/chiquito) ZKP DSL for more details.

To install and use, please ensure the following conditions are satisfied:

    - Rust installation: 
		+ Version: 1.83+
		+ Installation: https://rust-lang.org/tools/install/
		+ Check the installed version: `rustc --version`
		
	- Python installation:
		+ Version: 3.10+
		+ Installation: https://www.python.org/downloads/
		
	- Check PyO3:	https://pyo3.rs/v0.28.2/index.html

    - Create a new Python virtualenv: `python -m venv .venv` at a desired directory.
	- Load the environment: `source .venv/bin/activate`
	- Install `maturin`, just a Python package,  developed to work with PyO3 and provides the most "batteries included" experience, especially if you are aiming to publish to PyPI. https://www.maturin.rs/installation.html or https://pyo3.rs/main/getting-started

    Clone this re-designed Chiquito with `git clone https://github.com/thanhquanse/shin-chiquito.git`

    Make sure you are still in the virtualenv.
		+ Run `pip install -r requirements.txt` to install the required libraries.
		+ Run `maturin develop` to build the re-designed Chiquito.
	
	Note that the framework requires plonkish backend defined in `Cargo.toml`, which is fixed some bugs and tailored to the framework, so in case you use another, please make sure it is compatible.

# Fix build type annotation error if any
vi /<home>/.cargo/git/checkouts/zkp-sparql-plonkish-<c1a0bfd5c0d67691/e0125fe>/plonkish_backend/src/backend/hyperplonk/util.rs