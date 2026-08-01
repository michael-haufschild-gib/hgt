import GaloisForLFunctions.RHTower.SuzukiDonoghueSpectralMeasure
import GaloisForLFunctions.RHTower.SuzukiAntiPickIdentity
import GaloisForLFunctions.RHTower.SuzukiCrossResolventInstantiation

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

/-! ## Evenness, and the derivative formula of `(14)`

The hypothesis that the first moment vanishes is not an extra assumption: it is exactly what parity
of the spectral measure gives.  Pairing each atom with its reflection makes the moment its own
negative.

The displayed derivative of `(14)` is then the Cauchy combination's derivative, positive term by
term. -/

/-- **A reflection-odd family sums to zero.**  Pairing each index with its reflection makes the sum
its own negative; a fixed point contributes zero because the summand is odd there. -/
theorem sum_eq_zero_of_symmetric_odd {ι : Type*} (s : Finset ι) (f : ι → ℝ) (σ : ι → ι)
    (hmem : ∀ j ∈ s, σ j ∈ s) (hinv : ∀ j ∈ s, σ (σ j) = j)
    (hodd : ∀ j ∈ s, f (σ j) = -f j) :
    ∑ j ∈ s, f j = 0 := by
  refine Finset.sum_involution (fun a _ => σ a) (fun a ha => ?_) (fun a ha hne => ?_)
    (fun a ha => hmem a ha) (fun a ha => hinv a ha)
  · rw [hodd a ha]
    ring
  · intro hfix
    apply hne
    have h1 := hodd a ha
    rw [hfix] at h1
    linarith

/-- **Parity kills the first moment.**  If the atoms come in reflected pairs of equal mass, the
first moment vanishes — so `donoghuePurePoint_eq_cauchySum` applies with no further hypothesis. -/
theorem sum_moment_eq_zero_of_symmetric {ι : Type*} (s : Finset ι) (p t : ι → ℝ) (σ : ι → ι)
    (hmem : ∀ j ∈ s, σ j ∈ s) (hinv : ∀ j ∈ s, σ (σ j) = j)
    (hnode : ∀ j ∈ s, t (σ j) = -t j) (hmass : ∀ j ∈ s, p (σ j) = p j) :
    ∑ j ∈ s, t j * p j = 0 :=
  sum_eq_zero_of_symmetric_odd s (fun j => t j * p j) σ hmem hinv fun j hj => by
    rw [hnode j hj, hmass j hj]
    ring

/-- **The centre lies in the odd spectrum.**  A reflection-symmetric pure-point transform with no
atom at the origin vanishes there, so the origin is a zero — the card's forced central eigenvalue.
The reflected pair of any atom cancels against it exactly at the centre. -/
theorem cauchySum_eq_zero_at_center {ι : Type*} (s : Finset ι) (p t : ι → ℝ) (σ : ι → ι)
    (hmem : ∀ j ∈ s, σ j ∈ s) (hinv : ∀ j ∈ s, σ (σ j) = j)
    (hnode : ∀ j ∈ s, t (σ j) = -t j) (hmass : ∀ j ∈ s, p (σ j) = p j) :
    ∑ j ∈ s, nevanlinnaWeight (p j) (t j) / (t j - 0) = 0 := by
  refine sum_eq_zero_of_symmetric_odd s
    (fun j => nevanlinnaWeight (p j) (t j) / (t j - 0)) σ hmem hinv fun j hj => ?_
  rw [nevanlinnaWeight, nevanlinnaWeight, hnode j hj, hmass j hj, sub_zero, sub_zero]
  rw [show (1 : ℝ) + (-t j) ^ 2 = 1 + t j ^ 2 by ring]
  rw [div_neg]

/-- **`(14)`'s derivative formula.**  The transform's derivative is the sum of `(1+t²)p/(t-x)²`. -/
theorem hasDerivAt_donoghuePurePoint {ι : Type*} (s : Finset ι) (p t : ι → ℝ) (x : ℝ)
    (h : ∀ j ∈ s, t j - x ≠ 0) :
    HasDerivAt (fun y : ℝ => ∑ j ∈ s, nevanlinnaWeight (p j) (t j) / (t j - y))
      (∑ j ∈ s, nevanlinnaWeight (p j) (t j) / (t j - x) ^ 2) x :=
  _root_.RHTower.hasDerivAt_cauchySumReal s (fun j => nevanlinnaWeight (p j) (t j)) t x h

/-- **And it is positive**, which is the analytic content of `(14)`. -/
theorem deriv_donoghuePurePoint_pos {ι : Type*} (s : Finset ι) (p t : ι → ℝ) (x : ℝ)
    (h : ∀ j ∈ s, t j - x ≠ 0) (hp : ∀ j ∈ s, 0 < p j) (hne : s.Nonempty) :
    0 < ∑ j ∈ s, nevanlinnaWeight (p j) (t j) / (t j - x) ^ 2 :=
  _root_.RHTower.deriv_cauchySumReal_pos s (fun j => nevanlinnaWeight (p j) (t j)) t x h
    (fun j hj => nevanlinnaWeight_pos (hp j hj)) hne

/-- **The Cauchy form from parity alone.**  For a reflection-symmetric pure-point measure the
Donoghue transform is the Nevanlinna-weighted Cauchy combination, with no moment hypothesis. -/
theorem donoghuePurePoint_eq_cauchySum_of_symmetric {ι : Type*} (s : Finset ι) (p t : ι → ℝ)
    (σ : ι → ι) (hmem : ∀ j ∈ s, σ j ∈ s) (hinv : ∀ j ∈ s, σ (σ j) = j)
    (hnode : ∀ j ∈ s, t (σ j) = -t j) (hmass : ∀ j ∈ s, p (σ j) = p j)
    {z : ℂ} (hz : ∀ j ∈ s, ((t j : ℂ) - z) ≠ 0) :
    ∑ j ∈ s, suzukiDonoghueKernel (t j) z * ((p j : ℝ) : ℂ)
      = ∑ j ∈ s, ((nevanlinnaWeight (p j) (t j) : ℝ) : ℂ) / ((t j : ℂ) - z) :=
  donoghuePurePoint_eq_cauchySum s p t hz
    (sum_moment_eq_zero_of_symmetric s p t σ hmem hinv hnode hmass)

/-! ## The two divisors

Section 4's identification of the pole and zero divisors is algebra on the two-angle quotient: the
carrier vanishes exactly where the odd pencil does, and the two pencils share a zero exactly where
`A` and `E` do.  So the primeness of the source operator, which excludes common zeros of `A` and
`E`, is precisely what keeps the two divisors disjoint. -/

/-- **The carrier's zeros are the zeros of the odd pencil.** -/
theorem suzukiHerglotz_eq_zero_iff {A E : ℂ → ℂ} {z : ℂ}
    (hE : E z ≠ 0) (hW : suzukiCharacteristicPencil A E (-1) z ≠ 0) :
    suzukiHerglotz A E z = 0 ↔ suzukiCharacteristicPencil A E 1 z = 0 := by
  rw [suzukiHerglotz_eq_twoAngleDonoghueQuotient hE hW, neg_mul, neg_eq_zero,
    mul_eq_zero, div_eq_zero_iff]
  constructor
  · rintro (hI | (h1 | h2))
    · exact absurd hI Complex.I_ne_zero
    · exact h1
    · exact absurd h2 hW
  · intro h
    exact Or.inr (Or.inl h)

/-- **The two pencils share a zero exactly when `A` and `E` do.**  Hence excluding common zeros of
the source pair is exactly what makes the pole and zero divisors disjoint. -/
theorem pencil_common_zero_iff {A E : ℂ → ℂ} (z : ℂ) :
    (suzukiCharacteristicPencil A E 1 z = 0 ∧ suzukiCharacteristicPencil A E (-1) z = 0)
      ↔ (A z = 0 ∧ E z = 0) := by
  simp only [suzukiCharacteristicPencil, one_mul, neg_one_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linear_combination (h1 + h2) / 2, by linear_combination (h1 - h2) / 2⟩
  · rintro ⟨hA, hE⟩
    rw [hA, hE]
    norm_num

/-! ## The resolvent form of `(7)`

For a pure-point spectral measure the Donoghue transform is built from the resolvent by
`m = z + (z²+1)⟨(L-z)⁻¹g, g⟩`.  Once the resolvent pairing is the Cauchy combination of spectral
masses — which it is for an operator with an orthonormal eigenbasis — that expression is the sum of
the Donoghue kernels against the masses, provided the masses total one.

The total is one by Parseval, for a unit vector.  So the normalization of the deficiency vector is
exactly what makes the affine term of the Donoghue kernel come out right. -/

/-- **Parseval for the spectral masses.**  The squared coefficients of a vector in an orthonormal
eigenbasis sum to its squared norm — so a unit vector has masses totalling one, which is `(12)`. -/
theorem sum_spectralMass_eq_normSq {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : OrthonormalBasis (Fin n) ℝ V) (g : V) :
    ∑ i, inner ℝ (b i) g * inner ℝ (b i) g = ‖g‖ ^ 2 := by
  have h := b.sum_inner_mul_inner g g
  rw [real_inner_self_eq_norm_sq] at h
  simpa [real_inner_comm] using h

/-- **`(7)`, the resolvent form.**  With spectral masses totalling one, the Donoghue combination
`z + (z²+1)·(resolvent pairing)` is exactly the sum of the Donoghue kernels weighted by the masses.
The affine term `z` is absorbed precisely because the masses are a probability. -/
theorem donoghueResolvent_eq_kernelSum {ι : Type*} (s : Finset ι) (p t : ι → ℝ) (z : ℂ)
    (hp : ∑ j ∈ s, p j = 1) :
    z + (z ^ 2 + 1) * ∑ j ∈ s, ((p j : ℝ) : ℂ) / ((t j : ℂ) - z)
      = ∑ j ∈ s, suzukiDonoghueKernel (t j) z * ((p j : ℝ) : ℂ) := by
  have hterm : ∀ j ∈ s, suzukiDonoghueKernel (t j) z * ((p j : ℝ) : ℂ)
      = z * ((p j : ℝ) : ℂ) + (z ^ 2 + 1) * (((p j : ℝ) : ℂ) / ((t j : ℂ) - z)) := by
    intro j _
    rw [suzukiDonoghueKernel]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Complex.ofReal_sum, hp]
  push_cast
  ring

end GaloisForLFunctions.RHTower
