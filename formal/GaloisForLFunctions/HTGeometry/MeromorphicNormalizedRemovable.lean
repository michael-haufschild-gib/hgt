import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# A normalized removable-singularity criterion

If a meromorphic function satisfies `(z-p)f(z) → 0` on the punctured neighborhood, then it has
nonnegative meromorphic order at `p`. This is the zero-principal-part companion to the existing
simple-pole criterion for a nonzero normalized limit.
-/

open Complex Filter Topology

namespace GaloisForLFunctions

noncomputable section

theorem meromorphicOrderAt_nonneg_of_tendsto_mul_sub_zero
    {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (hlim : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 0)) :
    0 ≤ meromorphicOrderAt f p := by
  have hlin : MeromorphicAt (fun z : ℂ => z - p) p := by fun_prop
  have hprod : MeromorphicAt (fun z : ℂ => (z - p) * f z) p := hlin.mul hf
  have hpos : 0 < meromorphicOrderAt (fun z : ℂ => (z - p) * f z) p :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hprod).mp hlim
  change meromorphicOrderAt ((fun z : ℂ => z - p) * f) p > 0 at hpos
  rw [meromorphicOrderAt_mul hlin hf, meromorphicOrderAt_id_sub_const] at hpos
  by_cases htop : meromorphicOrderAt f p = ⊤
  · simp [htop]
  · lift meromorphicOrderAt f p to ℤ using htop with n hn
    have hpos' : (0 : ℤ) < 1 + n := by exact_mod_cast hpos
    exact_mod_cast (show (0 : ℤ) ≤ n by omega)

end

end GaloisForLFunctions
