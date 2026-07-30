import GaloisForLFunctions.HTGeometry.PolarOrbitSum
import GaloisForLFunctions.HTGeometry.FiniteDifferenceSurjective
import Mathlib

/-!
# The shift defects of `C(x)` form a torsion-free quotient

The shift and the derivation act on polar data by translating the pole and by raising the pole
order with a nonzero scalar.  Orbit sums are shift invariants and are moved one step up the order
filtration by the derivation, so a nonzero constant-coefficient differential operator can never
turn a datum with a nonvanishing orbit sum into a shift defect.

Consequently `C(x) / (sigma - 1) C(x)` is torsion free over `C[delta]`: if some `L(b)` is a shift
defect then so is `b`.
-/

open Polynomial
open scoped Classical Differential

namespace HTGeometry

variable {K : Type*} [Field K] [Algebra ℂ K]

/-! ## The derivation on polar data -/

/-- The polar datum of the derivative. -/
noncomputable def polarDeriv (d : ℂ) (c : (ℂ × ℕ) →₀ ℂ) : (ℂ × ℕ) →₀ ℂ :=
  c.sum fun p t => Finsupp.single (p.1, p.2 + 1) (-((p.2 + 1 : ℕ) : ℂ) * d * t)

theorem polarDeriv_apply_zero (d : ℂ) (c : (ℂ × ℕ) →₀ ℂ) (β : ℂ) :
    polarDeriv d c (β, 0) = 0 := by
  rw [polarDeriv, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp only [Finsupp.single_apply]
  rw [if_neg]
  intro hcon
  have h2 := congrArg Prod.snd hcon
  simp only at h2
  omega

theorem polarDeriv_apply_succ (d : ℂ) (c : (ℂ × ℕ) →₀ ℂ) (β : ℂ) (j : ℕ) :
    polarDeriv d c (β, j + 1) = -((j + 1 : ℕ) : ℂ) * d * c (β, j) := by
  rw [polarDeriv, Finsupp.sum_apply, Finsupp.sum]
  rw [Finset.sum_eq_single (β, j)]
  · simp
  · intro p _ hpne
    simp only [Finsupp.single_apply]
    rw [if_neg]
    intro hcon
    refine hpne ?_
    have h1 := congrArg Prod.fst hcon
    have h2 := congrArg Prod.snd hcon
    simp only at h1 h2
    exact Prod.ext h1 (by omega)
  · intro hnot
    simp [Finsupp.notMem_support_iff.mp hnot]

theorem orbSum_polarDeriv_zero (d : ℂ) (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) :
    orbSum (polarDeriv d c) α 0 = 0 := by
  rw [orbSum]
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hps, hp2, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨β, i⟩ := p
  simp only at hp2
  rw [hp2]
  exact polarDeriv_apply_zero d c β

theorem orbSum_polarDeriv_succ (d : ℂ) (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) :
    orbSum (polarDeriv d c) α (j + 1) = -((j + 1 : ℕ) : ℂ) * d * orbSum c α j := by
  set S : Finset (ℂ × ℕ) :=
    (c.support.filter (fun p : ℂ × ℕ => p.2 = j ∧ inOrbit α p.1)).image
      (fun p : ℂ × ℕ => (p.1, p.2 + 1)) with hS
  have hinj : ∀ p ∈ c.support.filter (fun p : ℂ × ℕ => p.2 = j ∧ inOrbit α p.1),
      ∀ q ∈ c.support.filter (fun p : ℂ × ℕ => p.2 = j ∧ inOrbit α p.1),
      (p.1, p.2 + 1) = (q.1, q.2 + 1) → p = q := by
    intro p _ q _ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    exact Prod.ext h1 (by omega)
  have hleft : orbSum (polarDeriv d c) α (j + 1) = ∑ q ∈ S, polarDeriv d c q := by
    refine orbSum_eq_sum_over ?_ ?_
    · intro q hq
      obtain ⟨hqs, hq2, hq1⟩ := Finset.mem_filter.mp hq
      obtain ⟨β, i⟩ := q
      simp only at hq2 hq1
      subst hq2
      refine Finset.mem_image.mpr ⟨(β, j), ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, rfl, hq1⟩
      refine Finsupp.mem_support_iff.mpr fun hc => ?_
      have := polarDeriv_apply_succ d c β j
      rw [hc, mul_zero] at this
      exact (Finsupp.mem_support_iff.mp hqs) this
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨-, hp2, hp1⟩ := Finset.mem_filter.mp hp
      exact ⟨by simp [hp2], hp1⟩
  rw [hleft, hS, Finset.sum_image hinj, orbSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨-, hp2, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨β, i⟩ := p
  simp only at hp2
  rw [hp2]
  exact polarDeriv_apply_succ d c β j

/-- Above the top pole order all orbit sums vanish. -/
theorem orbSum_eq_zero_of_lt (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) {j : ℕ}
    (hj : ∀ p ∈ c.support, p.2 < j) : orbSum c α j = 0 := by
  rw [orbSum]
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hps, hp2, -⟩ := Finset.mem_filter.mp hp
  exact absurd hp2 (Nat.ne_of_lt (hj p hps))

theorem orbSum_polarDeriv_iterate_lt (d : ℂ) (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) :
    ∀ n j : ℕ, j < n → orbSum ((polarDeriv d)^[n] c) α j = 0 := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
      intro j hj
      rw [Function.iterate_succ_apply']
      match j with
      | 0 => exact orbSum_polarDeriv_zero d _ α
      | (i + 1) =>
          rw [orbSum_polarDeriv_succ, ih i (by omega), mul_zero]

/-- The iterated derivative multiplies the orbit sum by an explicit nonzero scalar. -/
theorem orbSum_polarDeriv_iterate (d : ℂ) (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) :
    ∀ n j : ℕ, ∃ κ : ℂ, (d ≠ 0 → κ ≠ 0) ∧
      orbSum ((polarDeriv d)^[n] c) α (j + n) = κ * orbSum c α j := by
  intro n
  induction n with
  | zero => intro j; exact ⟨1, fun _ => one_ne_zero, by simp⟩
  | succ n ih =>
      intro j
      obtain ⟨κ, hκ, hval⟩ := ih j
      refine ⟨-((j + n + 1 : ℕ) : ℂ) * d * κ, ?_, ?_⟩
      · intro hd
        refine mul_ne_zero (mul_ne_zero ?_ hd) (hκ hd)
        exact neg_ne_zero.mpr ((Nat.cast_ne_zero (R := ℂ)).mpr (by omega))
      · rw [show j + (n + 1) = (j + n) + 1 from by omega, Function.iterate_succ_apply',
          orbSum_polarDeriv_succ, hval]
        ring

/-! ## The field bridge -/

section Bridge

variable {x : K} [Differential K] {d : ℂ}

theorem deriv_algebraMap_mul (hδc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0) (a : ℂ) (u : K) :
    (algebraMap ℂ K a * u)′ = algebraMap ℂ K a * u′ := by
  rw [Derivation.leibniz, hδc a]
  simp [smul_eq_mul]

theorem deriv_aeval (hδx : (x)′ = algebraMap ℂ K d)
    (hδc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0) (p : ℂ[X]) :
    (Polynomial.aeval x p)′
      = algebraMap ℂ K d * Polynomial.aeval x (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on with
  | C a => simp [hδc a]
  | add p q hp hq =>
      rw [map_add, Derivation.map_add, hp, hq, Polynomial.derivative_add, map_add, mul_add]
  | monomial n a ih =>
      set u : K := Polynomial.aeval x (Polynomial.C a * X ^ n) with hu
      have hlhs : Polynomial.aeval x (Polynomial.C a * X ^ (n + 1)) = u * x := by
        rw [hu, show Polynomial.C a * X ^ (n + 1) = (Polynomial.C a * X ^ n) * X from by ring,
          map_mul, Polynomial.aeval_X]
      have hrhs : Polynomial.derivative (Polynomial.C a * X ^ (n + 1))
          = Polynomial.C a * X ^ n + X * Polynomial.derivative (Polynomial.C a * X ^ n) := by
        rw [show Polynomial.C a * X ^ (n + 1) = (Polynomial.C a * X ^ n) * X from by ring,
          Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
        ring
      rw [hlhs, hrhs, Derivation.leibniz, hδx, ih, map_add, ← hu,
        show Polynomial.aeval x (X * Polynomial.derivative (Polynomial.C a * X ^ n))
            = x * Polynomial.aeval x (Polynomial.derivative (Polynomial.C a * X ^ n)) from by
          rw [map_mul, Polynomial.aeval_X]]
      simp only [smul_eq_mul]
      ring

theorem deriv_polarTerm (hx : Transcendental ℂ x) (hδx : (x)′ = algebraMap ℂ K d)
    (hδc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0) (α : ℂ) :
    ∀ j : ℕ, (polarTerm x α j)′
      = algebraMap ℂ K (-((j + 1 : ℕ) : ℂ) * d) * polarTerm x α (j + 1) := by
  have hne : x - algebraMap ℂ K α ≠ 0 := coord_sub_const_ne_zero hx α
  have hdx : (x - algebraMap ℂ K α)′ = algebraMap ℂ K d := by
    rw [Derivation.map_sub, hδx, hδc α, sub_zero]
  have hv : ((x - algebraMap ℂ K α)⁻¹)′
      = algebraMap ℂ K (-d) * ((x - algebraMap ℂ K α)⁻¹) ^ 2 := by
    have hprod : (x - algebraMap ℂ K α)⁻¹ * (x - algebraMap ℂ K α) = 1 :=
      inv_mul_cancel₀ hne
    have hd := congrArg (fun z : K => z′) hprod
    simp only [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, hdx] at hd
    have hD : (x - algebraMap ℂ K α) * ((x - algebraMap ℂ K α)⁻¹)′
        = -((x - algebraMap ℂ K α)⁻¹ * algebraMap ℂ K d) := by linear_combination hd
    have hmul := congrArg (fun z : K => (x - algebraMap ℂ K α)⁻¹ * z) hD
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at hmul
    rw [hmul, map_neg]
    ring
  intro j
  induction j with
  | zero =>
      simpa [polarTerm, map_neg] using hv
  | succ j ih =>
      have hsplit : polarTerm x α (j + 1) = polarTerm x α j * (x - algebraMap ℂ K α)⁻¹ := by
        rw [polarTerm, polarTerm, ← pow_succ]
      rw [hsplit, Derivation.leibniz, ih, hv]
      simp only [smul_eq_mul, map_neg, map_mul]
      rw [polarTerm, polarTerm, polarTerm]
      push_cast
      ring

end Bridge


theorem orbSum_smul (r : ℂ) (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) (j : ℕ) :
    orbSum (r • c) α j = r * orbSum c α j := by
  have hsub : (r • c).support ⊆ c.support := Finsupp.support_smul
  have h1 : orbSum (r • c) α j
      = ∑ p ∈ c.support.filter (fun p : ℂ × ℕ => p.2 = j ∧ inOrbit α p.1), (r • c) p := by
    refine orbSum_eq_sum_over ?_ ?_
    · intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hsub hq1, hq2⟩
    · intro q hq
      exact (Finset.mem_filter.mp hq).2
  rw [h1, orbSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by simp

/-- Orbit sums as an additive map. -/
noncomputable def orbSumHom (α : ℂ) (j : ℕ) : ((ℂ × ℕ) →₀ ℂ) →+ ℂ :=
  AddMonoidHom.mk' (fun c => orbSum c α j) (fun c d => orbSum_add c d α j)

@[simp] theorem orbSumHom_apply (α : ℂ) (j : ℕ) (c : (ℂ × ℕ) →₀ ℂ) :
    orbSumHom α j c = orbSum c α j := rfl

/-- Orbit sums vanish above the top pole order of the datum. -/
theorem orbSum_eq_zero_of_not_mem (c : (ℂ × ℕ) →₀ ℂ) (α : ℂ) {j : ℕ}
    (hj : j ∉ c.support.image Prod.snd) : orbSum c α j = 0 := by
  rw [orbSum]
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hps, hp2, -⟩ := Finset.mem_filter.mp hp
  exact absurd (Finset.mem_image.mpr ⟨p, hps, hp2⟩) hj

theorem aeval_mem_coordBase (x : K) (p : ℂ[X]) : Polynomial.aeval x p ∈ coordBase x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact mul_mem ((coordBase x).algebraMap_mem a) (pow_mem coord_mem_coordBase n)

/-- Polar sums as an additive map. -/
noncomputable def polarSumHom (x : K) : ((ℂ × ℕ) →₀ ℂ) →+ K :=
  AddMonoidHom.mk' (polarSum x) (polarSum_add x)

@[simp] theorem polarSumHom_apply (x : K) (c : (ℂ × ℕ) →₀ ℂ) :
    polarSumHom x c = polarSum x c := rfl

theorem polarTerm_mem_coordBase (x : K) (α : ℂ) (j : ℕ) :
    polarTerm x α j ∈ coordBase x := by
  rw [polarTerm]
  refine pow_mem (inv_mem (sub_mem coord_mem_coordBase ((coordBase x).algebraMap_mem α))) _

theorem polarSum_mem_coordBase (x : K) (c : (ℂ × ℕ) →₀ ℂ) :
    polarSum x c ∈ coordBase x := by
  rw [polarSum, Finsupp.sum]
  refine sum_mem fun p _ => mul_mem ((coordBase x).algebraMap_mem _)
    (polarTerm_mem_coordBase x p.1 p.2)

theorem sigma_polarTerm {x : K} (σ : K ≃ₐ[ℂ] K) (hσx : σ x = x + 1) (α : ℂ) (j : ℕ) :
    σ (polarTerm x α j) = polarTerm x (α - 1) j := by
  rw [polarTerm, polarTerm, map_pow, map_inv₀, map_sub, hσx, σ.commutes]
  congr 2
  rw [map_sub, map_one]
  ring

theorem sigma_polarSum {x : K} (σ : K ≃ₐ[ℂ] K) (hσx : σ x = x + 1) (c : (ℂ × ℕ) →₀ ℂ) :
    σ (polarSum x c) = polarSum x (polarShift c) := by
  have hmap : polarShift c
      = Finsupp.mapDomain ((Equiv.subRight (1 : ℂ)).prodCongr (Equiv.refl ℕ)) c := by
    rw [polarShift, Finsupp.equivMapDomain_eq_mapDomain]
  rw [hmap, polarSum, polarSum,
    Finsupp.sum_mapDomain_index_inj (Equiv.injective _)]
  rw [Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, σ.commutes, sigma_polarTerm σ hσx]
  rfl

section Bridge2

variable {x : K} [Differential K] {d : ℂ}

theorem deriv_polarSum (hx : Transcendental ℂ x) (hδx : (x)′ = algebraMap ℂ K d)
    (hδc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0) (c : (ℂ × ℕ) →₀ ℂ) :
    (polarSum x c)′ = polarSum x (polarDeriv d c) := by
  have hsplit := map_finsuppSum (polarSumHom x) c
    (fun p t => Finsupp.single ((p.1, p.2 + 1) : ℂ × ℕ) (-((p.2 + 1 : ℕ) : ℂ) * d * t))
  simp only [polarSumHom_apply] at hsplit
  rw [polarDeriv, hsplit]
  simp only [polarSum_single]
  rw [polarSum, Finsupp.sum, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [deriv_algebraMap_mul hδc, deriv_polarTerm hx hδx hδc]
  rw [← mul_assoc, ← map_mul]
  ring_nf

end Bridge2


theorem polarSum_sub (x : K) (c e : (ℂ × ℕ) →₀ ℂ) :
    polarSum x (c - e) = polarSum x c - polarSum x e := by
  have h := polarSum_add x (c - e) e
  rw [sub_add_cancel] at h
  linear_combination -h

section Classification

variable {x : K} [Differential K] {d : ℂ}

/-- The jets of a decomposed element split along the decomposition. -/
theorem jet_polar (hx : Transcendental ℂ x) (hδx : (x)′ = algebraMap ℂ K d)
    (hδc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0) (p : ℂ[X]) (c : (ℂ × ℕ) →₀ ℂ) :
    ∀ n : ℕ, (fun z : K => z′)^[n] (Polynomial.aeval x p + polarSum x c)
      = Polynomial.aeval x (Polynomial.C (d ^ n) * (Polynomial.derivative^[n] p))
        + polarSum x ((polarDeriv d)^[n] c) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [Derivation.map_add]
      rw [deriv_aeval hδx hδc, deriv_polarSum hx hδx hδc,
        Function.iterate_succ_apply' (f := polarDeriv d),
        Function.iterate_succ_apply' (f := (Polynomial.derivative : ℂ[X] → ℂ[X]))]
      congr 1
      rw [Polynomial.derivative_C_mul,
        show Polynomial.C (d ^ (n + 1)) = Polynomial.C d * Polynomial.C (d ^ n) from by
          rw [← Polynomial.C_mul, pow_succ]; ring_nf,
        mul_assoc]
      simp [map_mul]

/-- The rational subfield is closed under the derivation. -/
theorem coordBase_deriv_mem (hx : Transcendental ℂ x) (hδx : (x)′ = algebraMap ℂ K d)
    (hδc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0) {z : K} (hz : z ∈ coordBase x) :
    z′ ∈ coordBase x := by
  obtain ⟨p, c, rfl⟩ := exists_polarSum hx hz
  rw [Derivation.map_add, deriv_aeval hδx hδc, deriv_polarSum hx hδx hδc]
  exact add_mem (mul_mem ((coordBase x).algebraMap_mem d) (aeval_mem_coordBase x _))
    (polarSum_mem_coordBase x _)

/-- **Torsion freeness of the shift-defect quotient.**  If a nonzero constant-coefficient
differential operator sends `b` into the shift defects of `C(x)`, then `b` itself is a shift
defect. -/
theorem defect_of_operator_defect (hd : d ≠ 0) (hx : Transcendental ℂ x)
    (σ : K ≃ₐ[ℂ] K) (hσx : σ x = x + 1)
    (hδx : (x)′ = algebraMap ℂ K d) (hδc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0)
    {b u : K} (hb : b ∈ coordBase x) (hu : u ∈ coordBase x)
    {a : ℕ → ℂ} {N : ℕ} (haN : a N ≠ 0)
    (hrel : ∑ n ∈ Finset.range (N + 1),
        algebraMap ℂ K (a n) * (fun z : K => z′)^[n] b = σ u - u) :
    ∃ s ∈ coordBase x, σ s - s = b := by
  classical
  obtain ⟨pb, cb, hbdec⟩ := exists_polarSum hx hb
  obtain ⟨pu, cu, hudec⟩ := exists_polarSum hx hu
  set P : ℂ[X] := ∑ n ∈ Finset.range (N + 1),
    Polynomial.C (a n) * (Polynomial.C (d ^ n) * (Polynomial.derivative^[n] pb)) with hP
  set C : (ℂ × ℕ) →₀ ℂ := ∑ n ∈ Finset.range (N + 1),
    (a n) • ((polarDeriv d)^[n] cb) with hC
  have hLHS : ∑ n ∈ Finset.range (N + 1),
      algebraMap ℂ K (a n) * (fun z : K => z′)^[n] b
      = Polynomial.aeval x P + polarSum x C := by
    have hsum : polarSum x C
        = ∑ n ∈ Finset.range (N + 1), polarSum x ((a n) • ((polarDeriv d)^[n] cb)) := by
      have hms := map_sum (polarSumHom x)
        (fun n => (a n) • ((polarDeriv d)^[n] cb)) (Finset.range (N + 1))
      simp only [polarSumHom_apply] at hms
      rw [hC]
      exact hms
    rw [hP, map_sum, hsum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hbdec, jet_polar hx hδx hδc pb cb n, polarSum_smul, mul_add]
    simp [map_mul]
  have hRHS : σ u - u = Polynomial.aeval x (pu.comp (X + Polynomial.C 1) - pu)
      + polarSum x (polarDefect cu) := by
    rw [hudec, map_add, sigma_aeval_coord σ hσx, sigma_polarSum σ hσx, polarDefect,
      map_sub, polarSum_sub]
    ring
  rw [hLHS, hRHS] at hrel
  have hzero : Polynomial.aeval x (P - (pu.comp (X + Polynomial.C 1) - pu))
      + polarSum x (C - polarDefect cu) = 0 := by
    rw [map_sub, polarSum_sub]
    linear_combination hrel
  obtain ⟨-, hCeq⟩ := polar_injective hx hzero
  have hCdef : C = polarDefect cu := sub_eq_zero.mp hCeq
  have horbC : ∀ α j, orbSum C α j = 0 := by
    intro α j
    rw [hCdef]
    exact orbSum_polarDefect cu α j
  have horbcb : ∀ α j, orbSum cb α j = 0 := by
    set S : Finset ℕ := (cb.support.image Prod.snd).filter
      (fun j => ∃ α : ℂ, orbSum cb α j ≠ 0) with hS
    have hmemS : ∀ (β : ℂ) (i : ℕ), orbSum cb β i ≠ 0 → i ∈ S := by
      intro β i hbi
      refine Finset.mem_filter.mpr ⟨?_, β, hbi⟩
      by_contra hnot
      exact hbi (orbSum_eq_zero_of_not_mem cb β hnot)
    have key : S = ∅ := by
      by_contra hne
      have hSne : S.Nonempty := Finset.nonempty_of_ne_empty hne
      set M : ℕ := S.max' hSne with hM
      obtain ⟨-, α, hα⟩ := Finset.mem_filter.mp (S.max'_mem hSne)
      have hmax : ∀ (β : ℂ) (i : ℕ), M < i → orbSum cb β i = 0 := by
        intro β i hi
        by_contra hbi
        have hiS := hmemS β i hbi
        have := S.le_max' i hiS
        omega
      have hval : orbSum C α (M + N) = 0 := horbC α (M + N)
      have hsum : orbSum C α (M + N)
          = ∑ n ∈ Finset.range (N + 1),
              a n * orbSum ((polarDeriv d)^[n] cb) α (M + N) := by
        rw [hC]
        have hms := map_sum (orbSumHom α (M + N))
          (fun n => (a n) • ((polarDeriv d)^[n] cb)) (Finset.range (N + 1))
        simp only [orbSumHom_apply] at hms
        rw [hms]
        exact Finset.sum_congr rfl fun n _ => orbSum_smul _ _ _ _
      have hterm : ∀ n ∈ Finset.range (N + 1), n ≠ N →
          a n * orbSum ((polarDeriv d)^[n] cb) α (M + N) = 0 := by
        intro n hn hnN
        have hnlt : n < N := by
          simp only [Finset.mem_range] at hn
          omega
        obtain ⟨κ, -, hκ⟩ := orbSum_polarDeriv_iterate d cb α n (M + N - n)
        rw [show M + N = (M + N - n) + n from by omega, hκ,
          hmax α (M + N - n) (by omega), mul_zero, mul_zero]
      obtain ⟨κ, hκne, hκval⟩ := orbSum_polarDeriv_iterate d cb α N M
      rw [hsum, Finset.sum_eq_single N hterm (by simp), hκval] at hval
      exact (mul_ne_zero (mul_ne_zero haN (hκne hd)) hα) (by linear_combination hval)
    intro α j
    by_contra hne
    have := hmemS α j hne
    rw [key] at this
    exact absurd this (Finset.notMem_empty j)
  obtain ⟨cs, hcs⟩ :=
    exists_polarDefect_of_orbSum_eq_zero cb.support.card cb (le_refl _) horbcb
  obtain ⟨q, hq⟩ := exists_comp_sub_eq pb
  refine ⟨Polynomial.aeval x q + polarSum x cs, ?_, ?_⟩
  · exact add_mem (aeval_mem_coordBase x q) (polarSum_mem_coordBase x cs)
  · rw [map_add, sigma_aeval_coord σ hσx, sigma_polarSum σ hσx, hbdec, ← hq, ← hcs,
      polarDefect, map_sub, polarSum_sub, Polynomial.C_1]
    ring

end Classification

end HTGeometry
