"""ctypes wrapper around efx.so (see verifier.c for the checked definition)."""

import ctypes
import os

_MAXN, _MAXM = 6, 16
SLACK_UTOPIA = 1 << 40


class _EfxResult(ctypes.Structure):
    _fields_ = [
        ("count", ctypes.c_int64),
        ("nodes", ctypes.c_int64),
        ("min_slack", ctypes.c_int64),
        ("sum_slack", ctypes.c_int64),
        ("aborted", ctypes.c_int32),
        ("_pad", ctypes.c_int32),
    ]


_lib = None


def _load():
    global _lib
    if _lib is None:
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "efx.so")
        _lib = ctypes.CDLL(path)
        _lib.efx_verify.restype = ctypes.c_int
        _lib.efx_verify.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.POINTER(ctypes.c_int64),
            ctypes.c_int64, ctypes.c_int64, ctypes.c_int,
            ctypes.POINTER(_EfxResult), ctypes.POINTER(ctypes.c_uint8),
            ctypes.c_int64,
        ]
    return _lib


def verify(V, tau=1, cap=0, relation=0, collect=0):
    """V: n x m nested list/array of nonnegative ints.

    Returns dict with count/nodes/min_slack/sum_slack/aborted and, when
    collect > 0, 'allocs': list of tuples (agent id per good, original order).
    cap <= 0 means unlimited; relation: 0 = EFX, 1 = EF.
    """
    lib = _load()
    n = len(V)
    m = len(V[0])
    if not (1 <= n <= _MAXN and 1 <= m <= _MAXM):
        raise ValueError("dims out of range")
    flat = []
    for row in V:
        if len(row) != m:
            raise ValueError("ragged matrix")
        flat.extend(int(x) for x in row)
    arr = (ctypes.c_int64 * (n * m))(*flat)
    res = _EfxResult()
    buf = (ctypes.c_uint8 * (collect * m))() if collect > 0 else None
    rc = lib.efx_verify(n, m, arr, tau, cap, relation, ctypes.byref(res),
                        buf, collect if collect > 0 else 0)
    if rc != 0:
        raise RuntimeError(f"efx_verify rc={rc}")
    out = {
        "count": res.count,
        "nodes": res.nodes,
        "min_slack": res.min_slack,
        "sum_slack": res.sum_slack,
        "aborted": bool(res.aborted),
    }
    if collect > 0:
        k = min(res.count, collect)
        out["allocs"] = [tuple(buf[t * m: (t + 1) * m]) for t in range(k)]
    return out
