import GaloisForLFunctions.HTGeometry.MahlerDenominatorScale
import GaloisForLFunctions.HTGeometry.AlgebraicDenominator
import GaloisForLFunctions.HTGeometry.EulerADELinearization
import GaloisForLFunctions.HTGeometry.MvPolynomialTaylorFamily

/-!
# Graded denominator bounds for formal power series

A series is *Mahler-bounded of shift `t` and constant `e`* when it vanishes below index `t` and the
denominator of its `n`-th coefficient divides `e` times the Mahler weight at index `n - t`.  Shifts
add under multiplication, which is what turns the second-order vanishing of a Taylor defect into a
gain of two shifts.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

variable {C : ℕ} {A : ℕ → ℕ}

/-- The coefficients of `X` vanish below `t` and have denominators dividing `e` times the Mahler
weight shifted by `t`. -/
structure MahlerDen (C : ℕ) (A : ℕ → ℕ) (t e : ℕ) (X : PowerSeries ℂ) : Prop where
  vanish : ∀ n, n < t → PowerSeries.coeff n X = 0
  den : ∀ n, DenBy (e * mahlerScale C A (n - t)) (PowerSeries.coeff n X)

theorem MahlerDen.mono_const {t e e' : ℕ} {X : PowerSeries ℂ} (hee : e ∣ e')
    (h : MahlerDen C A t e X) : MahlerDen C A t e' X :=
  ⟨h.vanish, fun n => (h.den n).mono (mul_dvd_mul_right hee _)⟩

theorem MahlerDen.mono_shift {t t' e : ℕ} {X : PowerSeries ℂ} (htt : t' ≤ t)
    (h : MahlerDen C A t e X) : MahlerDen C A t' e X := by
  refine ⟨fun n hn => h.vanish n (by omega), fun n => ?_⟩
  refine (h.den n).mono (mul_dvd_mul_left e ?_)
  exact mahlerScale_dvd_of_le C A (by omega)

theorem MahlerDen.add {t e e' : ℕ} {X Z : PowerSeries ℂ}
    (hX : MahlerDen C A t e X) (hZ : MahlerDen C A t e' Z) :
    MahlerDen C A t (e * e') (X + Z) := by
  refine ⟨fun n hn => by rw [map_add, hX.vanish n hn, hZ.vanish n hn, add_zero], fun n => ?_⟩
  rw [map_add]
  refine DenBy.add ?_ ?_
  · exact (hX.den n).mono (mul_dvd_mul_right (Dvd.intro e' rfl) _)
  · exact (hZ.den n).mono (mul_dvd_mul_right (Dvd.intro_left e rfl) _)

theorem MahlerDen.add_same {t e : ℕ} {X Z : PowerSeries ℂ}
    (hX : MahlerDen C A t e X) (hZ : MahlerDen C A t e Z) :
    MahlerDen C A t e (X + Z) := by
  refine ⟨fun n hn => by rw [map_add, hX.vanish n hn, hZ.vanish n hn, add_zero], fun n => ?_⟩
  rw [map_add]
  exact DenBy.add (hX.den n) (hZ.den n)

theorem MahlerDen.neg {t e : ℕ} {X : PowerSeries ℂ} (hX : MahlerDen C A t e X) :
    MahlerDen C A t e (-X) :=
  ⟨fun n hn => by rw [map_neg, hX.vanish n hn, neg_zero], fun n => by
    rw [map_neg]; exact (hX.den n).neg⟩

theorem MahlerDen.sub {t e e' : ℕ} {X Z : PowerSeries ℂ}
    (hX : MahlerDen C A t e X) (hZ : MahlerDen C A t e' Z) :
    MahlerDen C A t (e * e') (X - Z) := by
  simpa [sub_eq_add_neg] using hX.add hZ.neg

theorem MahlerDen.zero (t e : ℕ) : MahlerDen C A t e (0 : PowerSeries ℂ) :=
  ⟨fun n _ => by simp, fun n => by simp⟩

theorem MahlerDen.one (e : ℕ) : MahlerDen C A 0 e (1 : PowerSeries ℂ) := by
  refine ⟨fun n hn => absurd hn (by omega), fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    simpa using denBy_of_isIntegral (x := (1 : ℂ)) isIntegral_one (e * mahlerScale C A 0)
  · simp [PowerSeries.coeff_one, hn]

theorem MahlerDen.mul {t t' e e' : ℕ} {X Z : PowerSeries ℂ}
    (hX : MahlerDen C A t e X) (hZ : MahlerDen C A t' e' Z) :
    MahlerDen C A (t + t') (e * e') (X * Z) := by
  classical
  have hzero : ∀ (n i j : ℕ), i + j = n → (n < t + t' ∨ i < t ∨ j < t') →
      PowerSeries.coeff i X * PowerSeries.coeff j Z = 0 := by
    intro n i j hij hcase
    rcases hcase with h | h | h
    · by_cases hi : i < t
      · rw [hX.vanish i hi, zero_mul]
      · rw [hZ.vanish j (by omega), mul_zero]
    · rw [hX.vanish i h, zero_mul]
    · rw [hZ.vanish j h, mul_zero]
  refine ⟨fun n hn => ?_, fun n => ?_⟩
  · rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero ?_
    rintro ⟨i, j⟩ hp
    exact hzero n i j (Finset.HasAntidiagonal.mem_antidiagonal.mp hp) (Or.inl hn)
  · rw [PowerSeries.coeff_mul]
    refine DenBy.sum ?_
    rintro ⟨i, j⟩ hp
    have hpn : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases hi : i < t
    · rw [hzero n i j hpn (Or.inr (Or.inl hi))]
      simp
    by_cases hj : j < t'
    · rw [hzero n i j hpn (Or.inr (Or.inr hj))]
      simp
    have hdvd : (e * mahlerScale C A (i - t)) * (e' * mahlerScale C A (j - t'))
        ∣ e * e' * mahlerScale C A (n - (t + t')) := by
      have hstep : mahlerScale C A (i - t) * mahlerScale C A (j - t')
          ∣ mahlerScale C A (n - (t + t')) := by
        refine dvd_trans (mahlerScale_mul_dvd C A (i - t) (j - t')) ?_
        refine mahlerScale_dvd_of_le C A ?_
        omega
      obtain ⟨k, hk⟩ := hstep
      exact ⟨k, by rw [hk]; ring⟩
    exact (DenBy.mul (hX.den i) (hZ.den j)).mono hdvd

theorem MahlerDen.sum {ι : Type*} {t e : ℕ} {s : Finset ι} {f : ι → PowerSeries ℂ}
    (h : ∀ i ∈ s, MahlerDen C A t e (f i)) : MahlerDen C A t e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using MahlerDen.zero (C := C) (A := A) t e
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := h a (Finset.mem_insert_self a s)
      have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      exact h1.add_same h2

theorem MahlerDen.eulerOp {t e : ℕ} {X : PowerSeries ℂ} (hX : MahlerDen C A t e X) :
    MahlerDen C A t e (formalEulerOp X) := by
  refine ⟨fun n hn => ?_, fun n => ?_⟩
  · rw [coeff_formalEulerOp, hX.vanish n hn, mul_zero]
  · rw [coeff_formalEulerOp]
    exact DenBy.natMul n (hX.den n)

theorem MahlerDen.eulerIterate {t e : ℕ} {X : PowerSeries ℂ} (hX : MahlerDen C A t e X)
    (j : ℕ) : MahlerDen C A t e (formalEulerOp^[j] X) := by
  induction j with
  | zero => simpa using hX
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact MahlerDen.eulerOp ih

theorem MahlerDen.eulerJet {m t e : ℕ} {X : PowerSeries ℂ} (hX : MahlerDen C A t e X)
    (j : Fin (m + 1)) : MahlerDen C A t e (eulerJetVector (m := m) X j) :=
  MahlerDen.eulerIterate hX (j : ℕ)

theorem MahlerDen.pow {t e : ℕ} {X : PowerSeries ℂ} (hX : MahlerDen C A t e X)
    (k : ℕ) : MahlerDen C A (k * t) (e ^ k) (X ^ k) := by
  induction k with
  | zero =>
      simpa using MahlerDen.one (C := C) (A := A) 1
  | succ k ih =>
      have hstep := MahlerDen.mul ih hX
      rw [← pow_succ, ← pow_succ] at hstep
      have hshift : (k * t + t) = (k + 1) * t := by ring
      rwa [hshift] at hstep

theorem MahlerDen.prod {ι : Type*} {s : Finset ι} {f : ι → PowerSeries ℂ} {tt g : ι → ℕ}
    (h : ∀ i ∈ s, MahlerDen C A (tt i) (g i) (f i)) :
    MahlerDen C A (∑ i ∈ s, tt i) (∏ i ∈ s, g i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using MahlerDen.one (C := C) (A := A) 1
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      exact MahlerDen.mul (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Series whose coefficient denominators are bounded by one constant. -/
def BoundedDenSeries (X : PowerSeries ℂ) : Prop :=
  ∃ e : ℕ, 0 < e ∧ ∀ n, DenBy e (PowerSeries.coeff n X)

theorem mahlerDen_of_boundedDen {e : ℕ} {X : PowerSeries ℂ}
    (h : ∀ n, DenBy e (PowerSeries.coeff n X)) : MahlerDen C A 0 e X := by
  refine ⟨fun n hn => absurd hn (by omega), fun n => ?_⟩
  exact (h n).mono (Dvd.intro _ rfl)

/-- The bounded-denominator series form a subsemiring. -/
def boundedDenSubsemiring : Subsemiring (PowerSeries ℂ) where
  carrier := {X | BoundedDenSeries X}
  zero_mem' := ⟨1, one_pos, fun n => by simp⟩
  one_mem' := ⟨1, one_pos, fun n => by
    by_cases hn : n = 0
    · subst hn
      simpa using denBy_of_isIntegral (x := (1 : ℂ)) isIntegral_one 1
    · simp [PowerSeries.coeff_one, hn]⟩
  add_mem' := by
    rintro X Z ⟨e, he, hX⟩ ⟨e', he', hZ⟩
    refine ⟨e * e', by positivity, fun n => ?_⟩
    rw [map_add]
    exact DenBy.add ((hX n).mono (Dvd.intro e' rfl)) ((hZ n).mono (Dvd.intro_left e rfl))
  mul_mem' := by
    rintro X Z ⟨e, he, hX⟩ ⟨e', he', hZ⟩
    refine ⟨e * e', by positivity, fun n => ?_⟩
    have h1 : MahlerDen 1 (fun _ => 1) 0 e X := mahlerDen_of_boundedDen hX
    have h2 : MahlerDen 1 (fun _ => 1) 0 e' Z := mahlerDen_of_boundedDen hZ
    have h3 := (MahlerDen.mul h1 h2).den n
    simpa [mahlerScale] using h3

theorem mem_boundedDenSubsemiring {X : PowerSeries ℂ} :
    X ∈ boundedDenSubsemiring ↔ BoundedDenSeries X := Iff.rfl

/-! ### Evaluation of a differential polynomial -/

theorem MahlerDen.aeval {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ℕ}
    {S : ι → PowerSeries ℂ} (hS : ∀ i, MahlerDen C A 0 e (S i))
    (Q : MvPolynomial ι (PowerSeries ℂ)) (hQ : ∀ d, MahlerDen C A 0 e (MvPolynomial.coeff d Q)) :
    MahlerDen C A 0 (e ^ (1 + Q.totalDegree)) (MvPolynomial.aeval S Q) := by
  classical
  have hEval : MvPolynomial.aeval S Q =
      ∑ d ∈ Q.support, MvPolynomial.coeff d Q * ∏ i ∈ d.support, S i ^ d i := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp
  rw [hEval]
  refine MahlerDen.sum ?_
  intro d hd
  have hpow : MahlerDen C A (∑ i ∈ d.support, 0) (∏ i ∈ d.support, e ^ d i)
      (∏ i ∈ d.support, S i ^ d i) := by
    refine MahlerDen.prod ?_
    intro i _
    simpa using MahlerDen.pow (hS i) (d i)
  have hprodpow : (∏ i ∈ d.support, e ^ d i) = e ^ (∑ i ∈ d.support, d i) :=
    Finset.prod_pow_eq_pow_sum d.support (fun i => d i) e
  rw [Finset.sum_const_zero, hprodpow] at hpow
  have hterm := MahlerDen.mul (hQ d) hpow
  rw [zero_add] at hterm
  refine hterm.mono_const ?_
  have hdeg : (∑ i ∈ d.support, d i) ≤ Q.totalDegree := by
    have := MvPolynomial.le_totalDegree (s := d) hd
    simpa [Finsupp.sum] using this
  have : e ^ (1 + ∑ i ∈ d.support, d i) ∣ e ^ (1 + Q.totalDegree) :=
    pow_dvd_pow e (by omega)
  calc e * e ^ (∑ i ∈ d.support, d i) = e ^ (1 + ∑ i ∈ d.support, d i) := by
        rw [pow_add, pow_one]
    _ ∣ e ^ (1 + Q.totalDegree) := this

/-- A finite family of bounded-denominator coefficients has one common denominator. -/
theorem exists_uniform_coeff_den {ι : Type*} (Q : MvPolynomial ι (PowerSeries ℂ))
    (h : ∀ d, BoundedDenSeries (MvPolynomial.coeff d Q)) :
    ∃ e : ℕ, 0 < e ∧ ∀ d n, DenBy e (PowerSeries.coeff n (MvPolynomial.coeff d Q)) := by
  classical
  choose ed hed hedd using h
  refine ⟨∏ d ∈ Q.support, ed d, Finset.prod_pos (fun d _ => hed d), fun d n => ?_⟩
  by_cases hd : d ∈ Q.support
  · exact (hedd d n).mono (Finset.dvd_prod_of_mem ed hd)
  · rw [MvPolynomial.notMem_support_iff.mp hd]
    simp

theorem MahlerDen.sum_of_exists {ι : Type*} {s : Finset ι} {t : ℕ} {f : ι → PowerSeries ℂ}
    (h : ∀ i ∈ s, ∃ e : ℕ, 0 < e ∧ MahlerDen C A t e (f i)) :
    ∃ e : ℕ, 0 < e ∧ MahlerDen C A t e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, one_pos, by simpa using MahlerDen.zero (C := C) (A := A) t 1⟩
  | insert a s ha ih =>
      obtain ⟨e₁, he₁, h₁⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨e₂, he₂, h₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine ⟨e₁ * e₂, by positivity, ?_⟩
      rw [Finset.sum_insert ha]
      exact h₁.add h₂

/-! ### The Taylor defect gains two shifts -/

/-- **The Taylor defect gains two shifts**, with a constant depending only on the differential
polynomial and the input constant. -/
theorem exists_taylorDefect_const {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : ∀ d, BoundedDenSeries (MvPolynomial.coeff d P)) (N e : ℕ) (he : 0 < e) :
    ∃ e' : ℕ, 0 < e' ∧ ∀ (C : ℕ) (A : ℕ → ℕ) (S L : Fin (m + 1) → PowerSeries ℂ),
      (∀ i, MahlerDen C A 0 e (S i)) → (∀ i, MahlerDen C A N e (L i)) →
      MahlerDen C A (2 * N) e' (taylorDefect S L P) := by
  classical
  obtain ⟨T, hT2, hTc, hTsum⟩ :=
    hasTaylorDefectFamily (A := PowerSeries ℂ) boundedDenSubsemiring P hP
  choose eα heα hcoeff using fun α => exists_uniform_coeff_den (T α) (fun d => hTc α d)
  refine ⟨∏ α ∈ T.support, ((e * eα α) ^ (1 + (T α).totalDegree) * e ^ jetDegree α),
    Finset.prod_pos fun α _ => mul_pos (pow_pos (mul_pos he (heα α)) _) (pow_pos he _), ?_⟩
  intro C A S L hS hL
  rw [hTsum S L, Finsupp.sum]
  refine MahlerDen.sum ?_
  intro α hα
  have hSe : ∀ i, MahlerDen C A 0 (e * eα α) (S i) :=
    fun i => (hS i).mono_const (Dvd.intro (eα α) rfl)
  have hQ : ∀ d, MahlerDen C A 0 (e * eα α) (MvPolynomial.coeff d (T α)) :=
    fun d => mahlerDen_of_boundedDen fun n => (hcoeff α d n).mono (Dvd.intro_left e rfl)
  have haev := MahlerDen.aeval (C := C) (A := A) hSe (T α) hQ
  have hmon : MahlerDen C A (∑ i ∈ α.support, α i * N) (∏ i ∈ α.support, e ^ α i)
      (jetMonomialValue L α) := by
    rw [jetMonomialValue, Finsupp.prod]
    exact MahlerDen.prod fun i _ => MahlerDen.pow (hL i) (α i)
  have hprodpow : (∏ i ∈ α.support, e ^ α i) = e ^ jetDegree α := by
    rw [Finset.prod_pow_eq_pow_sum, jetDegree, Finsupp.sum]
  have hsum : ∑ i ∈ α.support, α i * N = jetDegree α * N := by
    rw [jetDegree, Finsupp.sum, Finset.sum_mul]
  rw [hprodpow, hsum] at hmon
  have hprod := MahlerDen.mul haev hmon
  rw [zero_add] at hprod
  refine (hprod.mono_shift ?_).mono_const ?_
  · exact le_trans (Nat.mul_le_mul_right N (hT2 α hα)) (le_of_eq rfl)
  · exact Finset.dvd_prod_of_mem _ hα

end GaloisForLFunctions.HTGeometry
