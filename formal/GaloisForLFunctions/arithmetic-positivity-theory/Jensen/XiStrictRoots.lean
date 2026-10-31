import GaloisForLFunctions.RHTower.LaguerreShiftInterlacing
import GaloisForLFunctions.HTGeometry.LaguerreShiftSplits
import GaloisForLFunctions.HTGeometry.RealTaylorCoefficients
import GaloisForLFunctions.HTGeometry.PRecursiveDFinite
import GaloisForLFunctions.RHTower.LaguerrePolyaDivideRealZero
import GaloisForLFunctions.RHTower.OrderOneEvenLaguerrePolya
import GaloisForLFunctions.RHTower.XiCriticalGaussianNodes

/-!
# Repeated Xi Jensen roots falsify RH

Under RH every reversed Jensen section of Xi has real-root multiplicity at most one.
A repeated real root therefore falsifies RH, including when the section splits.

Multiplication by `z - a` acts as `D - a` on reversed Jensen sections. On a split
polynomial this operator lowers inherited multiplicities and creates only simple roots.
Extracting sufficiently many positive real Xi zeros from a Laguerre–Pólya quotient
therefore removes every repeated root. The required Xi zeros exist unconditionally.
-/

open Polynomial Finset Filter Topology Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace JensenStrict

/-- A nonzero real shift preserves nonzero polynomials, including constants. -/
theorem laguerreShift_ne_zero_of_nonzero {p : ℝ[X]} (hp : p ≠ 0)
    {β : ℝ} (hβ : β ≠ 0) : laguerreShift β p ≠ 0 := by
  by_cases hdeg : p.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    simp only [laguerreShift, derivative_C, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr hβ)
      (by rwa [← eq_C_of_natDegree_eq_zero hdeg]))
  · exact laguerreShift_ne_zero (by omega)

/-- At an inherited root, `D - β` lowers multiplicity by exactly one. -/
theorem rootMultiplicity_laguerreShift_of_root {p : ℝ[X]} {β x : ℝ}
    (hp : p ≠ 0) (hq : laguerreShift β p ≠ 0) (hx : p.IsRoot x) :
    (laguerreShift β p).rootMultiplicity x = p.rootMultiplicity x - 1 := by
  apply le_antisymm _ (le_rootMultiplicity_laguerreShift hp hq x)
  have hr : 0 < p.rootMultiplicity x := (rootMultiplicity_pos hp).mpr hx
  have hd : derivative p ≠ 0 := by
    intro hzero
    have heq := eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hzero)
    have hx' : (C (p.coeff 0) : ℝ[X]).IsRoot x := by rw [← heq]; exact hx
    have hval : p.coeff 0 = 0 := by simpa only [IsRoot, eval_C] using hx'
    exact hp (by rw [heq, hval, map_zero])
  by_contra hle
  have hmul : (X - C x) ^ p.rootMultiplicity x ∣ laguerreShift β p :=
    (le_rootMultiplicity_iff hq).mp (by omega)
  have hdvd : (X - C x) ^ p.rootMultiplicity x ∣ derivative p := by
    have h := dvd_add hmul ((pow_rootMultiplicity_dvd p x).mul_left (C β))
    simpa only [laguerreShift, sub_add_cancel] using h
  have h := (le_rootMultiplicity_iff hd).mpr hdvd
  rw [derivative_rootMultiplicity_of_root hx] at h
  omega

/-- Strict Laguerre positivity makes every newly created root simple. -/
theorem rootMultiplicity_laguerreShift_le_one_of_not_root {p : ℝ[X]} {β x : ℝ}
    (hsp : p.Splits) (hq : laguerreShift β p ≠ 0) (hx : p.eval x ≠ 0) :
    (laguerreShift β p).rootMultiplicity x ≤ 1 := by
  by_contra hle
  obtain ⟨hroot, hder⟩ := (one_lt_rootMultiplicity_iff_isRoot (t := x) hq).mp (by omega)
  have h0 : (derivative p).eval x = β * p.eval x := by
    simpa only [IsRoot, eval_laguerreShift, sub_eq_zero] using hroot
  have h1 : (derivative (derivative p)).eval x = β * (derivative p).eval x := by
    simpa only [IsRoot, laguerreShift, derivative_sub, derivative_C_mul,
      eval_sub, eval_mul, eval_C, sub_eq_zero] using hder
  have hdeg : 1 ≤ p.natDegree := by
    by_contra hn
    have hdeg0 : p.natDegree = 0 := by omega
    have heq := eq_C_of_natDegree_eq_zero hdeg0
    have heval : p.eval x = p.coeff 0 := by
      simpa only [eval_C] using congrArg (fun q : ℝ[X] => q.eval x) heq
    have hβp : β * p.coeff 0 = 0 := by
      have h := h0
      rw [derivative_eq_zero.mpr hdeg0, eval_zero, heval] at h
      exact h.symm
    exact hq (by rw [heq]; simp only [laguerreShift, derivative_C,
      ← map_mul, hβp, map_zero, sub_self])
  have hpos := RHTower.laguerreL1_eval_pos hsp hdeg hx
  simp only [RHTower.laguerreL1, eval_sub, eval_pow, eval_mul, h1, h0] at hpos
  nlinarith only [hpos]

theorem rootMultiplicity_laguerreShift_le {p : ℝ[X]} {β x : ℝ}
    (hsp : p.Splits) (hp : p ≠ 0) (hβ : β ≠ 0) :
    (laguerreShift β p).rootMultiplicity x ≤ max 1 (p.rootMultiplicity x - 1) := by
  have hq := laguerreShift_ne_zero_of_nonzero hp hβ
  by_cases hx : p.IsRoot x
  · rw [rootMultiplicity_laguerreShift_of_root hp hq hx]
    exact le_max_right _ _
  · exact (rootMultiplicity_laguerreShift_le_one_of_not_root hsp hq hx).trans
      (le_max_left _ _)

/-- Apply the real factors `D - a` in a finite list. -/
def shiftChain : List ℝ → ℝ[X] → ℝ[X]
  | [], p => p
  | a :: cs, p => laguerreShift a (shiftChain cs p)

theorem shiftChain_splits {p : ℝ[X]} (hsp : p.Splits) (cs : List ℝ) :
    (shiftChain cs p).Splits := by
  induction cs with
  | nil => exact hsp
  | cons a cs ih => exact splits_laguerreShift ih a

theorem shiftChain_ne_zero {p : ℝ[X]} (hp : p ≠ 0) {cs : List ℝ}
    (hcs : ∀ a ∈ cs, a ≠ 0) : shiftChain cs p ≠ 0 := by
  induction cs with
  | nil => exact hp
  | cons a cs ih =>
    exact laguerreShift_ne_zero_of_nonzero
      (ih (fun b hb => hcs b (List.mem_cons_of_mem _ hb)))
      (hcs a List.mem_cons_self)

/-- Each factor removes one unit of excess multiplicity; simple roots may move. -/
theorem rootMultiplicity_shiftChain_le {p : ℝ[X]} (hsp : p.Splits) (hp : p ≠ 0)
    {cs : List ℝ} (hcs : ∀ a ∈ cs, a ≠ 0) (x : ℝ) :
    (shiftChain cs p).rootMultiplicity x ≤ max 1 (p.rootMultiplicity x - cs.length) := by
  induction cs with
  | nil => simpa only [shiftChain, List.length_nil, Nat.sub_zero] using le_max_right 1 (p.rootMultiplicity x)
  | cons a cs ih =>
    have htail : ∀ b ∈ cs, b ≠ 0 := fun b hb => hcs b (List.mem_cons_of_mem _ hb)
    have hstep := rootMultiplicity_laguerreShift_le (x := x)
      (shiftChain_splits hsp cs) (shiftChain_ne_zero hp htail) (hcs a List.mem_cons_self)
    have hprev := ih htail
    change (laguerreShift a (shiftChain cs p)).rootMultiplicity x ≤ _
    rw [List.length_cons]
    omega

/-- At least `natDegree p` nonzero real factors remove every multiple root. -/
theorem rootMultiplicity_shiftChain_le_one {p : ℝ[X]} (hsp : p.Splits) (hp : p ≠ 0)
    {cs : List ℝ} (hcs : ∀ a ∈ cs, a ≠ 0) (hlen : p.natDegree ≤ cs.length) (x : ℝ) :
    (shiftChain cs p).rootMultiplicity x ≤ 1 := by
  have h := rootMultiplicity_shiftChain_le hsp hp hcs x
  have hm : p.rootMultiplicity x ≤ p.natDegree := by
    rw [← count_roots]
    exact (Multiset.count_le_card x p.roots).trans p.card_roots'
  omega

theorem realTaylorCoeff_id_mul_zero (F : ℂ → ℂ) :
    realTaylorCoeff (fun z => z * F z) 0 = 0 := by
  simp [realTaylorCoeff]

theorem realTaylorCoeff_id_mul_succ {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n : ℕ) :
    realTaylorCoeff (fun z => z * F z) (n + 1) = realTaylorCoeff F n := by
  unfold realTaylorCoeff
  rw [iteratedDeriv_id_mul_zero hF n, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  congr 1
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

theorem realTaylorCoeff_const_mul (F : ℂ → ℂ) (a : ℝ) (n : ℕ) :
    realTaylorCoeff (fun z => (a : ℂ) * F z) n = a * realTaylorCoeff F n := by
  unfold realTaylorCoeff
  rw [iteratedDeriv_const_mul_field]
  rw [mul_left_comm, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem jensenReverse_sub (c e : ℕ → ℝ) (d : ℕ) :
    jensenReverse (fun i => c i - e i) d = jensenReverse c d - jensenReverse e d := by
  simp only [jensenReverse, sub_mul, map_sub, sum_sub_distrib]

theorem jensenReverse_mul (c : ℕ → ℝ) (a : ℝ) (d : ℕ) :
    jensenReverse (fun i => a * c i) d = C a * jensenReverse c d := by
  simp only [jensenReverse, mul_sum, mul_assoc, map_mul]

/-- Shifting Taylor coefficients by one differentiates the reversed section. -/
theorem jensenReverse_shift (c : ℕ → ℝ) (d : ℕ) :
    jensenReverse (fun i => if i = 0 then 0 else c (i - 1)) d =
      derivative (jensenReverse c d) := by
  rw [jensenReverse, Finset.sum_range_succ', jensenReverse, map_sum, Finset.sum_range_succ]
  simp only [Nat.succ_ne_zero, ↓reduceIte,
    Nat.add_sub_cancel, zero_mul, map_zero,
    Nat.sub_self, pow_zero, mul_one, derivative_C, add_zero]
  apply sum_congr rfl
  intro i hi
  rw [derivative_C_mul, derivative_X_pow, Nat.descFactorial_succ, Nat.cast_mul]
  simp only [← mul_assoc, ← C_mul, Nat.sub_sub]
  congr 2
  ring

theorem realTaylorCoeff_linear_mul {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (a : ℝ) (n : ℕ) :
    realTaylorCoeff (fun z => (z - (a : ℂ)) * F z) n =
      (if n = 0 then 0 else realTaylorCoeff F (n - 1)) - a * realTaylorCoeff F n := by
  have heq : (fun z => (z - (a : ℂ)) * F z) =
      (fun z => z * F z) - (fun z => (a : ℂ) * F z) := by funext z; simp [sub_mul]
  have hd₁ : Differentiable ℂ (fun z => z * F z) := differentiable_id.mul hF
  have hd₂ : Differentiable ℂ (fun z => (a : ℂ) * F z) := hF.const_mul _
  have hsub : realTaylorCoeff ((fun z => z * F z) - (fun z => (a : ℂ) * F z)) n =
      realTaylorCoeff (fun z => z * F z) n -
        realTaylorCoeff (fun z => (a : ℂ) * F z) n := by
    unfold realTaylorCoeff
    rw [iteratedDeriv_sub (hd₁.contDiff.contDiffAt) (hd₂.contDiff.contDiffAt),
      mul_sub, Complex.sub_re]
  rw [heq, hsub, realTaylorCoeff_const_mul]
  cases n with
  | zero => simp only [realTaylorCoeff_id_mul_zero, ↓reduceIte]
  | succ n => simp only [realTaylorCoeff_id_mul_succ hF, Nat.succ_ne_zero,
      ↓reduceIte, Nat.add_sub_cancel]

/-- A real linear factor of an entire function becomes a real Laguerre shift. -/
theorem jensenReverse_linear_mul {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (a : ℝ) (d : ℕ) :
    jensenReverse (realTaylorCoeff (fun z => (z - (a : ℂ)) * F z)) d =
      laguerreShift a (jensenReverse (realTaylorCoeff F) d) := by
  have heq := funext (realTaylorCoeff_linear_mul hF a)
  rw [heq, jensenReverse_sub, jensenReverse_shift, jensenReverse_mul]
  rfl

theorem coeff_jensenReverse_top (c : ℕ → ℝ) (d : ℕ) :
    (jensenReverse c d).coeff d = c 0 := by
  rw [jensenReverse, finsetSum_coeff]
  rw [sum_eq_single 0]
  · simp
  · intro i hi hne
    have hid : i ≤ d := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hdi : d ≠ d - i := by omega
    simp only [coeff_C_mul_X_pow, if_neg hdi]
  · intro h
    exact False.elim (h (mem_range.mpr (Nat.succ_pos d)))

theorem jensenReverse_ne_zero {F : ℂ → ℂ}
    (hs : ∀ z, F (conj z) = conj (F z)) (hzero : F 0 ≠ 0) (d : ℕ) :
    jensenReverse (realTaylorCoeff F) d ≠ 0 := by
  intro h
  have hc : realTaylorCoeff F 0 = 0 := by
    rw [← coeff_jensenReverse_top (realTaylorCoeff F) d, h, coeff_zero]
  have hreal := ofReal_realTaylorCoeff hs 0
  simp only [hc, Complex.ofReal_zero, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_mul, iteratedDeriv_zero] at hreal
  exact hzero hreal.symm

/-- Multiply an entire function by the real linear factors in a list. -/
def realFactorChain : List ℝ → (ℂ → ℂ) → ℂ → ℂ
  | [], F => F
  | a :: cs, F => fun z => (z - (a : ℂ)) * realFactorChain cs F z

theorem dslope_schwarzReal {F : ℂ → ℂ}
    (hs : ∀ z, F (conj z) = conj (F z)) (a : ℝ) :
    ∀ z, dslope F (a : ℂ) (conj z) = conj (dslope F (a : ℂ) z) := by
  have ha : conj (F (a : ℂ)) = F (a : ℂ) := by
    simpa only [Complex.conj_ofReal] using (hs (a : ℂ)).symm
  intro z
  by_cases hz : z = (a : ℂ)
  · subst z
    simp only [Complex.conj_ofReal, dslope_same]
    have h := iteratedDeriv_conj_of_schwarzReal hs 1 (a : ℂ)
    simpa only [iteratedDeriv_one, Complex.conj_ofReal] using h
  · have hcz : conj z ≠ (a : ℂ) := by
      intro h
      apply hz
      simpa using congrArg conj h
    rw [dslope_of_ne F hcz, dslope_of_ne F hz]
    simp only [slope_def_field, hs, map_div₀, map_sub, Complex.conj_ofReal, ha]

theorem mul_dslope_of_zero {F : ℂ → ℂ} {a : ℂ} (ha : F a = 0) (z : ℂ) :
    (z - a) * dslope F a z = F z := by
  simpa only [smul_eq_mul, ha, sub_zero] using sub_smul_dslope F a z

/-- Removing finitely many positive real zeros preserves the LP quotient and its value at zero. -/
theorem exists_realFactorChain {F : ℂ → ℂ}
    (hLP : LaguerrePolya F) (hs : ∀ z, F (conj z) = conj (F z))
    (hzero : F 0 ≠ 0) (hinf : {x : ℝ | 0 < x ∧ F (x : ℂ) = 0}.Infinite)
    (d : ℕ) :
    ∃ (cs : List ℝ) (G : ℂ → ℂ), cs.length = d ∧
      (∀ a ∈ cs, 0 < a) ∧ LaguerrePolya G ∧
      (∀ z, G (conj z) = conj (G z)) ∧ G 0 ≠ 0 ∧ F = realFactorChain cs G := by
  induction d generalizing F with
  | zero => exact ⟨[], F, rfl, by simp, hLP, hs, hzero, rfl⟩
  | succ d ih =>
    obtain ⟨a, ha, hFa⟩ := hinf.nonempty
    let G := dslope F (a : ℂ)
    have hG : LaguerrePolya G := RHTower.laguerrePolya_dslope hLP hzero hFa
    have hsG := dslope_schwarzReal hs a
    have hGzero : G 0 ≠ 0 := by
      intro h
      change dslope F (a : ℂ) 0 = 0 at h
      apply hzero
      rw [← mul_dslope_of_zero hFa 0, h, mul_zero]
    have hinfG : {x : ℝ | 0 < x ∧ G (x : ℂ) = 0}.Infinite := by
      apply (hinf.sdiff (finite_singleton a)).mono
      intro x hx
      refine ⟨hx.1.1, ?_⟩
      have hxa : (x : ℂ) ≠ (a : ℂ) := by
        exact_mod_cast (show x ≠ a from hx.2)
      change dslope F (a : ℂ) (x : ℂ) = 0
      rw [dslope_of_ne F hxa, slope_def_field, hx.1.2, hFa, sub_self, zero_div]
    obtain ⟨cs, H, hlen, hpos, hH, hsH, hH0, hfactor⟩ :=
      ih hG hsG hGzero hinfG
    refine ⟨a :: cs, H, by simp only [List.length_cons, hlen],
      ?_, hH, hsH, hH0, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hpos b hb
    · funext z
      change F z = (z - (a : ℂ)) * realFactorChain cs H z
      rw [← hfactor]
      exact (mul_dslope_of_zero hFa z).symm

theorem realFactorChain_differentiable {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (cs : List ℝ) :
    Differentiable ℂ (realFactorChain cs F) := by
  induction cs with
  | nil => exact hF
  | cons a cs ih => exact (differentiable_id.sub_const (a : ℂ)).mul ih

theorem jensenReverse_realFactorChain {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (cs : List ℝ) (d : ℕ) :
    jensenReverse (realTaylorCoeff (realFactorChain cs F)) d =
      shiftChain cs (jensenReverse (realTaylorCoeff F) d) := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    change jensenReverse (realTaylorCoeff (fun z =>
      (z - (a : ℂ)) * realFactorChain cs F z)) d = _
    rw [jensenReverse_linear_mul (realFactorChain_differentiable hF cs), ih]
    rfl

theorem jensenReverse_splits {F : ℂ → ℂ} (hF : LaguerrePolya F)
    (hs : ∀ z, F (conj z) = conj (F z)) (d : ℕ) :
    (jensenReverse (realTaylorCoeff F) d).Splits := by
  have h := Splits.reflect (splits_jensenPoly_realTaylorCoeff hF hs d)
    (natDegree_jensenPoly_le (realTaylorCoeff F) d)
  rwa [← reflect_jensenReverse, reflect_reflect] at h

/-- Infinitely many real zeros force every reversed Jensen section to have simple roots. -/
theorem jensenReverse_rootMultiplicity_le_one {F : ℂ → ℂ}
    (hLP : LaguerrePolya F) (hs : ∀ z, F (conj z) = conj (F z))
    (hzero : F 0 ≠ 0) (hinf : {x : ℝ | 0 < x ∧ F (x : ℂ) = 0}.Infinite)
    (d : ℕ) (x : ℝ) :
    (jensenReverse (realTaylorCoeff F) d).rootMultiplicity x ≤ 1 := by
  obtain ⟨cs, G, hlen, hpos, hG, hsG, hG0, heq⟩ :=
    exists_realFactorChain hLP hs hzero hinf d
  rw [heq, jensenReverse_realFactorChain hG.differentiable]
  apply rootMultiplicity_shiftChain_le_one (jensenReverse_splits hG hsG d)
    (jensenReverse_ne_zero hsG hG0 d)
  · exact fun a ha => (hpos a ha).ne'
  · rw [hlen]
    exact natDegree_jensenReverse_le _ _


end JensenStrict

namespace RHTower

theorem xiJensenReverse_rootMultiplicity_le_one_of_rh
    (hRH : RiemannHypothesis) (d : ℕ) (x : ℝ) :
    (jensenReverse (realTaylorCoeff XiC) d).rootMultiplicity x ≤ 1 :=
  JensenStrict.jensenReverse_rootMultiplicity_le_one
    (riemannHypothesis_iff_laguerrePolya_XiC.mp hRH) XiC_conj XiC_zero_ne
    infinite_positive_real_XiC_zeros d x

/-- A repeated real root obstructs RH even when the finite section splits. -/
theorem not_riemannHypothesis_of_xiJensenReverse_multiple_root :
    (∃ (d : ℕ) (x : ℝ),
      1 < (jensenReverse (realTaylorCoeff XiC) d).rootMultiplicity x) →
      ¬ RiemannHypothesis := by
  rintro ⟨d, x, hx⟩ hRH
  exact (not_lt_of_ge (xiJensenReverse_rootMultiplicity_le_one_of_rh hRH d x)) hx

end RHTower

#print axioms JensenStrict.rootMultiplicity_laguerreShift_le
#print axioms JensenStrict.rootMultiplicity_shiftChain_le_one
#print axioms JensenStrict.jensenReverse_linear_mul
#print axioms JensenStrict.exists_realFactorChain
#print axioms RHTower.xiJensenReverse_rootMultiplicity_le_one_of_rh
#print axioms RHTower.not_riemannHypothesis_of_xiJensenReverse_multiple_root
