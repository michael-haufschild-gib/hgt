import GaloisForLFunctions.RHTower.SuzukiDonoghueSpectralMeasure
import GaloisForLFunctions.RHTower.SuzukiAntiPickIdentity

/-!
# Canonical interlacing of the two Suzuki extension spectra

For a pure-point spectral measure the Donoghue transform collapses to a Cauchy combination with the
Nevanlinna weights `(1+t²)p`.  The subtracted linear part `∑ t p` vanishes when the measure is even,
which is exactly the parity the normalized Herglotz quotient enjoys.

Once the transform is a positive-weight Cauchy combination, the interlacing is not a new analytic
fact: such a combination is strictly increasing off its nodes and blows up at each of them, so it
has exactly one zero between consecutive poles.  The poles are the spectrum of the even extension
and the zeros that of the odd one, so the two canonical spectra strictly interlace.
-/

namespace GaloisForLFunctions.RHTower

open Set

/-- The Nevanlinna weight of an atom: the spectral mass scaled by `1 + t²`. -/
noncomputable def nevanlinnaWeight (p t : ℝ) : ℝ := (1 + t ^ 2) * p

theorem nevanlinnaWeight_pos {p t : ℝ} (hp : 0 < p) : 0 < nevanlinnaWeight p t := by
  rw [nevanlinnaWeight]
  positivity

/-- **The pure-point Donoghue transform is a Cauchy combination.**  Termwise the kernel splits as
the Nevanlinna kernel minus the node, and the subtracted part sums to zero exactly when the measure
has vanishing first moment — which evenness supplies. -/
theorem donoghuePurePoint_eq_cauchySum {ι : Type*} (s : Finset ι) (p t : ι → ℝ) {z : ℂ}
    (hz : ∀ j ∈ s, ((t j : ℂ) - z) ≠ 0) (hodd : ∑ j ∈ s, t j * p j = 0) :
    ∑ j ∈ s, suzukiDonoghueKernel (t j) z * ((p j : ℝ) : ℂ)
      = ∑ j ∈ s, ((nevanlinnaWeight (p j) (t j) : ℝ) : ℂ) / ((t j : ℂ) - z) := by
  have hterm : ∀ j ∈ s, suzukiDonoghueKernel (t j) z * ((p j : ℝ) : ℂ)
      = ((nevanlinnaWeight (p j) (t j) : ℝ) : ℂ) / ((t j : ℂ) - z)
        - ((t j * p j : ℝ) : ℂ) := by
    intro j hj
    rw [suzukiDonoghueKernel_eq_nevanlinna (hz j hj), nevanlinnaWeight]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have hlin : ∑ j ∈ s, ((t j * p j : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sum, hodd, Complex.ofReal_zero]
  rw [hlin, sub_zero]

/-- **`(14)`, the canonical interlacing.**  Between two consecutive atoms of a positive pure-point
spectral measure the Donoghue transform has exactly one real zero.  The poles are the even-extension
spectrum and the zeros the odd one, so the two canonical Suzuki spectra strictly interlace. -/
theorem existsUnique_zero_in_atomGap {ι : Type*} [DecidableEq ι] (s : Finset ι) (p t : ι → ℝ)
    {i k : ι} (hi : i ∈ s) (hk : k ∈ s) (hp : ∀ j ∈ s, 0 < p j) (hti : Set.InjOn t ↑s)
    (hlt : t i < t k) (hgap : ∀ j ∈ s, t j ∉ Ioo (t i) (t k)) :
    ∃! c : ℝ, c ∈ Ioo (t i) (t k) ∧
      (∑ j ∈ s, nevanlinnaWeight (p j) (t j) / (t j - c)) = 0 :=
  _root_.RHTower.existsUnique_zero_in_gap s (fun j => nevanlinnaWeight (p j) (t j)) t hi hk
    (fun j hj => nevanlinnaWeight_pos (hp j hj)) hti hlt hgap

/-- The transform is strictly increasing between consecutive atoms: its derivative is the sum of
`(1+t²)p/(t-x)²`, which is positive.  This is the uniqueness half of the interlacing, and it needs
no ordering of the atoms. -/
theorem strictMonoOn_donoghuePurePoint {ι : Type*} (s : Finset ι) (p t : ι → ℝ) {S : Set ℝ}
    (hS : Convex ℝ S) (hnode : ∀ x ∈ S, ∀ j ∈ s, t j - x ≠ 0)
    (hp : ∀ j ∈ s, 0 < p j) (hne : s.Nonempty) :
    StrictMonoOn (fun x : ℝ => ∑ j ∈ s, nevanlinnaWeight (p j) (t j) / (t j - x)) S :=
  _root_.RHTower.strictMonoOn_cauchySumReal s (fun j => nevanlinnaWeight (p j) (t j)) t hS hnode
    (fun j hj => nevanlinnaWeight_pos (hp j hj)) hne

/-- The transform has no nonreal zeros: off the real axis its imaginary part carries the sign of
`Im z`.  With the interlacing this accounts for the whole zero set. -/
theorem cauchySum_nevanlinna_ne_zero_of_im_ne_zero {ι : Type*} (s : Finset ι) (p t : ι → ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (hp : ∀ j ∈ s, 0 < p j) (hne : s.Nonempty) :
    (∑ j ∈ s, ((nevanlinnaWeight (p j) (t j) : ℝ) : ℂ) / ((t j : ℂ) - z)) ≠ 0 :=
  _root_.RHTower.cauchySum_ne_zero_of_im_ne_zero s (fun j => nevanlinnaWeight (p j) (t j)) t hz
    (fun j hj => nevanlinnaWeight_pos (hp j hj)) hne

end GaloisForLFunctions.RHTower
