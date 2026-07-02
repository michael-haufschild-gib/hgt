"""Generate Lean square-tree viability certificates (tasks #34/#35)."""
import numpy as np, math
from fractions import Fraction as F

def rup(x, den=10**4):   return F(math.ceil(float(x)*den), den)
def rdown(x, den=10**4): return F(math.floor(float(x)*den), den)

def lf(q):
    q = F(q)
    if q < 0:
        return f"(-{-q.numerator}/{q.denominator})" if q.denominator != 1 else f"(-{-q.numerator})"
    return f"({q.numerator}/{q.denominator})" if q.denominator != 1 else f"({q.numerator})"

class Gen:
    def __init__(self, bx, bi, name):
        self.bx, self.bi = F(bx), F(bi)
        self.bf = complex(self.bx, self.bi)
        self.name = name
        self.lines = []
        self.ctr = 0
        self.Nb = rup(abs(self.bf)*1.000001)
        assert self.Nb**2 >= self.bx**2+self.bi**2
        self.S = rup(np.sqrt(1+4*float(self.Nb))*1.000001)
        assert self.S**2 >= 1+4*self.Nb
        self.X = (1+self.S)/2

    def fresh(self):
        self.ctr += 1
        return f"nd{self.ctr}"

    def chain_ok(self, c0, r0, maxd=14):
        xs = float(self.X)
        c, r = complex(c0), float(r0)
        for d in range(maxd):
            r = r*(2*abs(c)+r)*1.001 + 5e-4
            c = c*c+self.bf
            if abs(c)-r > xs + 1e-3: return d+1
            if r > abs(c)+xs: return 0
        return 0

    def emit_chain(self, cx, ci, h):
        out = ["  refine U0DiskEscape.escape_square_coords (by norm_num) ?_ z hre him"]
        r = F(283,200)*h
        c = (F(cx), F(ci))
        for _ in range(20):
            M = rdown(np.sqrt(float(c[0]**2+c[1]**2))*0.999999)
            if M >= 0 and M*M <= c[0]**2+c[1]**2 and self.X + r < M:
                out.append(f"  exact U0DiskEscape.escape_terminal_coords (M := {lf(M)}) (Nb := {lf(self.Nb)}) (S := {lf(self.S)})"
                           " (by norm_num) (by norm_num) (by norm_num) (by norm_num)"
                           " (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
                return out
            ex = c[0]*c[0]-c[1]*c[1]+self.bx
            ei = 2*c[0]*c[1]+self.bi
            nx = F(round(float(ex)*10**4), 10**4)
            ni = F(round(float(ei)*10**4), 10**4)
            drift2 = (ex-nx)**2 + (ei-ni)**2
            E = rup(np.sqrt(float(drift2))*1.05 + 1e-6)
            assert E*E >= drift2
            N = rup(np.sqrt(float(c[0]**2+c[1]**2))*1.000001)
            assert N*N >= c[0]**2+c[1]**2
            rp = rup(float(E + r*(2*N+r))*1.001)
            assert rp >= E + r*(2*N+r)
            out.append(f"  refine U0DiskEscape.escape_step_coords (c'x := {lf(nx)}) (c'i := {lf(ni)}) (r' := {lf(rp)}) (E := {lf(E)}) (N := {lf(N)})"
                       " (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_")
            c, r = (nx, ni), rp
        raise RuntimeError("chain too long")

    def node(self, cx, cy, h):
        cx, cy, h = F(cx), F(cy), F(h)
        nm = f"{self.name}_nd{self.ctr + 1}"
        self.ctr += 1
        B = f"(⟨{lf(self.bx)}, {lf(self.bi)}⟩ : ℂ)"
        hdr = (f"private theorem {nm} : ∀ z : ℂ, |z.re - {lf(cx)}| ≤ {lf(h)} → |z.im - {lf(cy)}| ≤ {lf(h)} → "
               f"‖z‖ ≤ 1 → z ∉ filledJulia {B} := by")
        dx, dy = abs(cx)-h, abs(cy)-h
        if dx > 1:
            self.lines += [hdr, "  intro z hre _ hz",
                "  exact absurd hz (U0DiskEscape.square_outside_unit_re (by norm_num) z hre)", ""]
            return nm
        if dy > 1:
            self.lines += [hdr, "  intro z _ him hz",
                "  exact absurd hz (U0DiskEscape.square_outside_unit_im (by norm_num) z him)", ""]
            return nm
        if dx >= 0 and dy >= 0 and dx*dx+dy*dy > 1:
            self.lines += [hdr, "  intro z hre him hz",
                f"  exact absurd hz (U0DiskEscape.square_outside_unit_corner (dx := {lf(dx)}) (dy := {lf(dy)})"
                " (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) z hre him)", ""]
            return nm
        if self.chain_ok(complex(cx,cy), float(F(283,200)*h)):
            body = ["  intro z hre him _"] + self.emit_chain(cx, cy, h)
            self.lines += [hdr] + body + [""]
            return nm
        if h < F(1, 4096): raise RuntimeError(f"hmin at ({cx},{cy},{h})")
        h2 = h/2
        kids = [self.node(cx-h2, cy-h2, h2), self.node(cx-h2, cy+h2, h2),
                self.node(cx+h2, cy-h2, h2), self.node(cx+h2, cy+h2, h2)]
        self.lines += [hdr, "  intro z hre him hz",
            "  rcases U0DiskEscape.interval_split hre with h1 | h1 <;>",
            "    rcases U0DiskEscape.interval_split him with h2 | h2"]
        glue = ("(by rcases abs_le.mp h1 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith) "
                "(by rcases abs_le.mp h2 with ⟨ha, hb⟩; rw [abs_le]; constructor <;> linarith)")
        for k in kids:
            self.lines.append(f"  · exact {k} z {glue} hz")
        self.lines.append("")
        return nm

    def theorem(self, doc):
        B = f"(⟨{lf(self.bx)}, {lf(self.bi)}⟩ : ℂ)"
        pre = len(self.lines)
        root = self.node(0, 0, 1)
        body = self.lines[pre:]
        self.lines = self.lines[:pre]
        out = body
        out += [f"/-- {doc} -/",
                f"theorem {self.name} : ∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia {B} :=",
                f"  U0DiskEscape.viable_of_root_square {root}"]
        return "\n".join(out)

HEADER = """/-
# Slice viability instances along `arg b` at modulus ≈ 3 — GENERATED FILE

Machine-generated square-tree escape certificates (generator:
`computations/rho_curve_recon/gen_slice.py`); every proof is rational arithmetic through the
coordinate-form disk-escape kit (`U0DiskEscape`).  Do not edit by hand — regenerate.
-/
import GaloisForLFunctions.U0.U0DiskEscape

open Complex Set Bottcher

namespace U0DichotomySlice

set_option maxHeartbeats 1000000

"""

POINTS_A = [
    ("-7/9",     "29/10",   "slice_viable_105", "arg b ≈ 105.02°, ‖b‖ ≈ 3.0025"),
    ("-12/7",    "22/9",    "slice_viable_125", "arg b ≈ 125.05°, ‖b‖ ≈ 2.9860"),
    ("-23/10",   "27/14",   "slice_viable_140", "arg b ≈ 140.03°, ‖b‖ ≈ 3.0017"),
    ("-13/5",    "3/2",     "slice_viable_150", "arg b ≈ 150.02°, ‖b‖ ≈ 3.0017"),
]
POINTS_B = [
    ("-273/100", "156/125", "slice_viable_155", "arg b ≈ 155.43°, ‖b‖ ≈ 3.0017"),
]

def build(points, path):
    chunks = [HEADER]
    total = 0
    for bx, bi, name, doc in points:
        g = Gen(bx, bi, name)
        chunks.append(g.theorem(f"Viable slice point: {doc} — the closed unit disk escapes.") + "\n")
        total += g.ctr
        print(f"  {name}: nodes={g.ctr}")
    chunks.append("end U0DichotomySlice")
    open(path, "w").write("\n".join(chunks) + "\n")
    print(f"wrote {path} (total nodes {total})")

if __name__ == "__main__":
    base = "/Users/Spare/Documents/code/riemann/publications/hgt/formal/GaloisForLFunctions/U0/"
    build(POINTS_A, base + "U0SliceViableA.lean")
    build(POINTS_B, base + "U0SliceViableB.lean")
