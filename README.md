# LZT to FunPay Resale

Current source snapshot of the LZT Market to FunPay resale plugin for FunPay
Cardinal.

## Contents

- `plugins/lzt_to_fp_resale.py` - plugin source.
- `requirements-lzt-to-funpay.txt` - extra Python dependencies.

The plugin creates runtime files under `storage/plugins/lzt_to_fp_resale`.
Those files can contain account credentials, order history, cookies, tokens,
and customer data. They are intentionally excluded from this repository.

## Install

Copy the plugin into the Cardinal `plugins` directory and install the extra
dependencies:

```bash
python3 -m pip install -r requirements-lzt-to-funpay.txt
```

Configure the plugin through Cardinal after installation. Do not commit
runtime JSON files, `.env` files, logs, backups, or exported account data.
