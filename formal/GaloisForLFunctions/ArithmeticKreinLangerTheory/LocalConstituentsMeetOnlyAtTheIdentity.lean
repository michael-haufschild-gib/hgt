import GaloisForLFunctions.ArithmeticKreinLangerTheory.CyclicSubgroupsDecideTheKreinLangerClass
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexUnderRotationDampingAndCoalescence
import GaloisForLFunctions.HeckeKreinToeplitz.TheMarginIsTheWidthOfTheIndexOneWindow

/-!
# Local constituents meet only at the identity

The prime side of the Weil kernel is assembled from one constituent per prime, each supported on its
tower `⟨p⟩`. On `⊕_p ℤ` two distinct towers meet only at the identity. This module isolates what such
assemblies can and cannot do.

**The Euler factor is a Poisson kernel** (`isPosDefKernel_poissonKernel`, `isPosDefKernel_eulerKernel`).
`n ↦ r^{|n|}`, `0 ≤ r ≤ 1`, is positive definite on `ℤ`: on points `z_a ∈ ℕ` (after a Hecke shift) its
form is `(1 − r²) Σ_{k<N} |h(k)|² + |h(N)|²` with `h(k) = Σ_{z_b ≤ k} c_b r^{k−z_b}`
(`poisson_pair`, the geometric identity `(1 − r²) Σ_{i<L} r^{2i} + r^{2L} = 1` per pair). The local
kernel of `(1 − p^{−s})^{−1}` is `L_p(n) = log p · p^{−|n|/2}`; the prime constituent of the Weil kernel
on `⟨p⟩` is `log p · δ₀ − L_p`. Every unitary twin `ω^n L_p` is again positive definite
(`isPosDefKernel_twist`): local positive definiteness is twin-invariant.

**Zero-or-infinity law** (`negIndex_eq_zero_or_top_of_isAxisSupported`). On `ℤ^S` with `|S| ≥ 2`, a
kernel vanishing off the coordinate axes has index `0` or `∞`. A negative family, translated along
the diagonal `(1, …, 1)` by multiples of a large step, gives translates whose differences have every
coordinate nonzero, hence lie off every axis: the translates are mutually orthogonal
(`card_le_negIndex_of_orthogonal_translates`).

**No finite set of places has finite index** (`negIndex_localAssembly_eq_top`). The assembly
`Σ_{p∈S} a_p (δ₀ − L_p)` of local constituents (`a_p > 0`, `0 < r_p < 1`) on `ℤ^S`, `|S| ≥ 2`, vanishes
at the identity and is negative on the pair `0, e_p`; by the law it has infinite index. Finite nonzero
index is therefore a non-local phenomenon: it needs a constituent supported off the towers, and in
the Weil kernel that constituent is the archimedean factor. With one tower the law fails: on `ℤ`
every kernel is axis-supported and a single hyperbolic pair has index one (`rankOne_axis_pair`), as
over `𝔽_q`, where all data live on the one Frobenius tower.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-! ### The Poisson kernel -/

/-- The Poisson kernel `n ↦ r^{|n|}` on `ℤ`. -/
def poissonKernel (r : ℝ) (n : Multiplicative ℤ) : ℂ :=
  ((r ^ (Multiplicative.toAdd n).natAbs : ℝ) : ℂ)

/-- **The geometric identity per pair.** For `z, w ≤ N`,
`(1 − r²) Σ_{k<N} [z,w ≤ k] r^{k−z} r^{k−w} + r^{N−z} r^{N−w} = r^{(M−z)+(M−w)}`, `M = max z w`. -/
theorem poisson_pair (r : ℝ) (z w : ℕ) :
    ∀ N, max z w ≤ N → (1 - r ^ 2) * ∑ k ∈ range N,
      (if z ≤ k ∧ w ≤ k then r ^ (k - z) * r ^ (k - w) else 0) + r ^ (N - z) * r ^ (N - w) =
        r ^ ((max z w - z) + (max z w - w)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    rw [sum_eq_zero fun k hk => if_neg fun h => by have := mem_range.mp hk; omega, mul_zero,
      zero_add, ← pow_add]
  | succ N hle ih =>
    rw [Finset.sum_range_succ, if_pos ⟨by omega, by omega⟩, show N + 1 - z = N - z + 1 by omega,
      show N + 1 - w = N - w + 1 by omega, pow_succ, pow_succ]
    linear_combination ih

/-- **The Poisson kernel is positive definite.** -/
theorem isPosDefKernel_poissonKernel {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsPosDefKernel (poissonKernel r) := by
  refine ⟨fun n => by simp [poissonKernel, toAdd_inv, Int.natAbs_neg], fun n x c => ?_⟩
  -- shift the family into `ℕ`
  set B : ℤ := ∑ a, |Multiplicative.toAdd (x a)| with hB
  set u : Multiplicative ℤ := Multiplicative.ofAdd B with hu
  rw [← gram_mul_left _ x u]
  have hpos : ∀ a, 0 ≤ Multiplicative.toAdd (u * x a) := fun a => by
    have h1 := single_le_sum (f := fun a => |Multiplicative.toAdd (x a)|)
      (fun _ _ => abs_nonneg _) (mem_univ a)
    have h2 := neg_abs_le (Multiplicative.toAdd (x a))
    simp only [hu, toAdd_mul, toAdd_ofAdd]
    linarith
  set z : Fin n → ℕ := fun a => (Multiplicative.toAdd (u * x a)).toNat with hzdef
  have hz : ∀ a, (z a : ℤ) = Multiplicative.toAdd (u * x a) := fun a =>
    Int.toNat_of_nonneg (hpos a)
  set N : ℕ := ∑ a, z a with hN
  have hzN : ∀ a, z a ≤ N := fun a => single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)
  set h : ℕ → ℂ := fun k => ∑ b, c b * (if z b ≤ k then ((r ^ (k - z b) : ℝ) : ℂ) else 0) with hh
  -- the two sides of the identity, entry by entry
  set T : ℕ → Fin n → Fin n → ℂ := fun k a b => conj (c a) * c b *
    (((if z a ≤ k ∧ z b ≤ k then r ^ (k - z a) * r ^ (k - z b) else 0 : ℝ)) : ℂ) with hT
  have hsq : ∀ k, conj (h k) * h k = ∑ a, ∑ b, T k a b := fun k => by
    rw [hh, map_sum, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    simp only [hT, map_mul, apply_ite (starRingEnd ℂ), Complex.conj_ofReal, map_zero]
    by_cases ha : z a ≤ k <;> by_cases hb : z b ≤ k <;> simp [ha, hb]
    ring
  have hentry : ∀ a b, conj (c a) * poissonKernel r ((u * x a)⁻¹ * (u * x b)) * c b =
      ((1 - r ^ 2 : ℝ) : ℂ) * ∑ k ∈ range N, T k a b + T N a b := fun a b => by
    have hdist : (Multiplicative.toAdd ((u * x a)⁻¹ * (u * x b))).natAbs =
        (max (z a) (z b) - z a) + (max (z a) (z b) - z b) := by
      rw [toAdd_mul, toAdd_inv, ← hz, ← hz]; omega
    have key := poisson_pair r (z a) (z b) N (max_le (hzN a) (hzN b))
    simp only [hT, poissonKernel, hdist, ← key, if_pos (⟨hzN a, hzN b⟩ : z a ≤ N ∧ z b ≤ N),
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum, ← mul_sum]
    ring
  rw [hermQuad_gram]
  have hswap : ∑ a, ∑ b, ∑ k ∈ range N, T k a b = ∑ k ∈ range N, ∑ a, ∑ b, T k a b :=
    calc ∑ a, ∑ b, ∑ k ∈ range N, T k a b = ∑ a, ∑ k ∈ range N, ∑ b, T k a b :=
          sum_congr rfl fun a _ => sum_comm
      _ = _ := sum_comm
  have hsum : ∑ a, ∑ b, conj (c a) * poissonKernel r ((u * x a)⁻¹ * (u * x b)) * c b =
      ((1 - r ^ 2 : ℝ) : ℂ) * ∑ k ∈ range N, conj (h k) * h k + conj (h N) * h N :=
    calc _ = ∑ a, ∑ b, (((1 - r ^ 2 : ℝ) : ℂ) * ∑ k ∈ range N, T k a b + T N a b) :=
          sum_congr rfl fun a _ => sum_congr rfl fun b _ => hentry a b
      _ = ((1 - r ^ 2 : ℝ) : ℂ) * ∑ a, ∑ b, ∑ k ∈ range N, T k a b + ∑ a, ∑ b, T N a b := by
          simp only [sum_add_distrib, mul_sum]
      _ = _ := by rw [hswap]; simp only [hsq]
  rw [hsum, add_re, re_ofReal_mul, re_sum]
  have hnn : ∀ k, 0 ≤ (conj (h k) * h k).re := fun k => by
    rw [mul_comm, Complex.mul_conj]; exact Complex.normSq_nonneg _
  exact add_nonneg (mul_nonneg (by nlinarith) (sum_nonneg fun k _ => hnn k)) (hnn N)

/-- A unitary character twists a positive-definite kernel into a positive-definite kernel. -/
theorem isPosDefKernel_twist {G : Type*} [Group G] {χ : G →* ℂ} (hχ : IsUnitaryChar χ)
    {k : G → ℂ} (hk : IsPosDefKernel k) : IsPosDefKernel fun u => χ u * k u := by
  refine (isPosDefKernel_iff fun u => ?_).mpr ((negIndex_twist hχ k).trans hk.negIndex_eq_zero)
  show χ u⁻¹ * k u⁻¹ = conj (χ u * k u)
  have hinv : (χ u)⁻¹ = conj (χ u) := by
    simpa using inv_conj_of_norm_eq_one (z := conj (χ u)) (by rw [Complex.norm_conj]; exact hχ u)
  rw [hk.1 u, map_mul, map_inv_eq_inv, hinv]

/-- The local kernel `L_p(n) = log p · p^{−|n|/2}` of the Euler factor `(1 − p^{−s})^{−1}`, whose
logarithmic derivative has coefficients `log p · p^{−k/2}` at `p^{±k}` on the critical line. -/
def eulerKernel (p : ℕ) (n : Multiplicative ℤ) : ℂ :=
  (Real.log p : ℂ) * poissonKernel ((p : ℝ) ^ (-(1 / 2 : ℝ))) n

/-- **The local Euler-factor kernel is positive definite**, and so is every unitary twin of it. -/
theorem isPosDefKernel_eulerKernel {p : ℕ} (hp : 1 ≤ p) : IsPosDefKernel (eulerKernel p) :=
  IsPosDefKernel.ofReal_mul (isPosDefKernel_poissonKernel (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp) (by norm_num)))
    (Real.log_nonneg (by exact_mod_cast hp))

/-- The prime constituent of the Weil kernel on the tower of `p`: `log p · δ₀ − L_p`, which vanishes
at the identity. -/
def primeConstituent (p : ℕ) (n : Multiplicative ℤ) : ℂ :=
  (if n = 1 then (Real.log p : ℂ) else 0) - eulerKernel p n

theorem primeConstituent_one (p : ℕ) : primeConstituent p 1 = 0 := by
  simp [primeConstituent, eulerKernel, poissonKernel]

/-! ### The zero-or-infinity law -/

/-- A kernel on `ℤ^S` is **axis-supported** when it vanishes off the coordinate axes. -/
def IsAxisSupported {S : Type*} (k : Multiplicative (S → ℤ) → ℂ) : Prop :=
  ∀ v, k v ≠ 0 → ∃ s, ∀ t, t ≠ s → Multiplicative.toAdd v t = 0

/-- **The zero-or-infinity law.** On `ℤ^S` with at least two coordinates, an axis-supported kernel
is positive definite or has infinitely many negative squares. -/
theorem negIndex_eq_zero_or_top_of_isAxisSupported {S : Type*} [Fintype S] {p q : S}
    (hpq : p ≠ q) {k : Multiplicative (S → ℤ) → ℂ} (hk : IsAxisSupported k) :
    negIndex k = 0 ∨ negIndex k = ⊤ := by
  classical
  by_cases h0 : negIndex k = 0
  · exact Or.inl h0
  right
  obtain ⟨n, x, c, hc⟩ : ∃ (n : ℕ) (x : Fin n → Multiplicative (S → ℤ)) (c : Fin n → ℂ),
      hermQuad (gram k x) c < 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 (negIndex_eq_zero_iff.mpr hcon)
  set B : ℤ := ∑ a, ∑ s, |Multiplicative.toAdd (x a) s| + 1 with hB
  have hBle : ∀ a s, |Multiplicative.toAdd (x a) s| < B := fun a s => by
    have h1 := single_le_sum (f := fun s => |Multiplicative.toAdd (x a) s|)
      (fun _ _ => abs_nonneg _) (mem_univ s)
    have h2 := single_le_sum (f := fun a => ∑ s, |Multiplicative.toAdd (x a) s|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ a)
    linarith
  refine ENat.eq_top_iff_forall_ge.mpr fun m => ?_
  have := card_le_negIndex_of_orthogonal_translates hc
    (fun j : Fin m => Multiplicative.ofAdd (fun _ : S => 2 * B * (j : ℤ))) fun j j' hjj' a b => by
      by_contra hne
      obtain ⟨s, hs⟩ := hk _ hne
      obtain ⟨t, hts⟩ : ∃ t, t ≠ s := by
        by_cases hps : p = s
        · exact ⟨q, fun h => hpq (hps.trans h.symm)⟩
        · exact ⟨p, hps⟩
      have ht := hs t hts
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply] at ht
      have hd : (j : ℤ) ≠ j' := fun h => hjj' (Fin.ext (by exact_mod_cast h))
      have ha := abs_lt.mp (hBle a t)
      have hb := abs_lt.mp (hBle b t)
      rcases lt_or_gt_of_ne hd with hlt | hlt <;> nlinarith
  simpa using this

/-! ### Finite assemblies of local constituents -/

/-- The local constituent `a(δ₀ − r^{|v_s|})` of place `s`, supported on the axis of `s`. -/
def axisConstituent {S : Type*} [Fintype S] [DecidableEq S] (a r : ℝ) (s : S)
    (v : Multiplicative (S → ℤ)) : ℂ :=
  if ∀ t, t ≠ s → Multiplicative.toAdd v t = 0 then
    (a : ℂ) * ((if Multiplicative.toAdd v s = 0 then 1 else 0) -
      ((r ^ (Multiplicative.toAdd v s).natAbs : ℝ) : ℂ))
  else 0

/-- The assembly `Σ_s a_s (δ₀ − L_s)` of finitely many local constituents on `ℤ^S`. -/
def localAssembly {S : Type*} [Fintype S] [DecidableEq S] (a r : S → ℝ)
    (v : Multiplicative (S → ℤ)) : ℂ :=
  ∑ s, axisConstituent (a s) (r s) s v

theorem isAxisSupported_localAssembly {S : Type*} [Fintype S] [DecidableEq S] (a r : S → ℝ) :
    IsAxisSupported (localAssembly a r) := fun v hv => by
  by_contra hcon
  push Not at hcon
  exact hv (sum_eq_zero fun s _ => by
    obtain ⟨t, hts, ht⟩ := hcon s
    rw [axisConstituent, if_neg fun h => ht (h t hts)])

/-- The unit vector of a place. -/
def unitVec {S : Type*} [DecidableEq S] (s : S) : Multiplicative (S → ℤ) :=
  Multiplicative.ofAdd (Pi.single s 1)

/-- **No finite set of places has finite index.** With at least two places, local masses `a_s > 0`
and radii `r_s > 0`, the assembly of local constituents has infinitely many negative squares: it
vanishes at the identity and equals `−a_p r_p` at `±e_p`, so the pair `0, e_p` is negative. -/
theorem negIndex_localAssembly_eq_top {S : Type*} [Fintype S] [DecidableEq S] {p q : S}
    (hpq : p ≠ q) {a r : S → ℝ} (ha : ∀ s, 0 < a s) (hr : ∀ s, 0 < r s) :
    negIndex (localAssembly a r) = ⊤ := by
  refine (negIndex_eq_zero_or_top_of_isAxisSupported hpq
    (isAxisSupported_localAssembly a r)).resolve_left fun h0 => ?_
  have hzero : localAssembly a r 1 = 0 := sum_eq_zero fun s _ => by
    simp [axisConstituent]
  have hval : ∀ v : Multiplicative (S → ℤ), v = unitVec p ∨ v = (unitVec p)⁻¹ →
      localAssembly a r v = -((a p : ℂ) * ((r p : ℝ) : ℂ)) := fun v hv => by
    have hvp : (Multiplicative.toAdd v p).natAbs = 1 := by
      rcases hv with rfl | rfl <;> simp [unitVec, toAdd_inv]
    have hvt : ∀ t, t ≠ p → Multiplicative.toAdd v t = 0 := fun t ht => by
      rcases hv with rfl | rfl <;> simp [unitVec, toAdd_inv, ht]
    rw [localAssembly, Finset.sum_eq_single p]
    · have hne : Multiplicative.toAdd v p ≠ 0 := fun h => by simp [h] at hvp
      rw [axisConstituent, if_pos hvt, if_neg hne, hvp, pow_one]
      ring
    · intro s _ hsp
      rw [axisConstituent, if_neg]
      push Not
      exact ⟨p, fun h => hsp h.symm, fun h => by simp [h] at hvp⟩
    · simp
  have h2 := negIndex_eq_zero_iff.mp h0 2 ![1, unitVec p] fun _ => 1
  rw [hermQuad_gram] at h2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, one_mul,
    mul_one, inv_one, inv_mul_cancel, hzero, hval _ (Or.inl rfl), hval _ (Or.inr rfl)] at h2
  simp only [add_re, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    zero_add, add_zero] at h2
  nlinarith [mul_pos (ha p) (hr p)]

/-- **The law needs two towers.** On `ℤ` (one place) every kernel is axis-supported, and the
hyperbolic pair of the character `n ↦ 2^n` has index exactly one. -/
theorem rankOne_axis_pair :
    ∃ k : Multiplicative (Unit → ℤ) → ℂ, IsAxisSupported k ∧ negIndex k = 1 := by
  set χ : Multiplicative (Unit → ℤ) →* ℂ :=
    { toFun := fun v => (2 : ℂ) ^ Multiplicative.toAdd v ()
      map_one' := by simp
      map_mul' := fun v w => by simp [zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0)] }
  refine ⟨pairKernel χ 1, fun v _ => ⟨(), fun t ht => absurd (Subsingleton.elim t ()) ht⟩, ?_⟩
  have hχ : ¬ IsUnitaryChar χ := fun h => by
    have := h (Multiplicative.ofAdd fun _ => 1)
    simp [χ] at this
  simpa using negIndex_add_pairKernel_eq_one isPosDefKernel_zero hχ one_ne_zero

end GaloisForLFunctions.ArithmeticKreinLangerTheory

#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.negIndex_eq_zero_or_top_of_isAxisSupported
#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.negIndex_localAssembly_eq_top
#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.rankOne_axis_pair
