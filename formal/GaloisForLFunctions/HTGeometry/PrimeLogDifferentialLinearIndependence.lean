import GaloisForLFunctions.HTGeometry.PrimeLogTranslationGeometry
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator

/-!
# Differential-linear independence of prime-log translates

Exact simple poles and the private-pole theorem imply that no nontrivial finite
constant-coefficient differential combination of distinct complex translates of the prime-log
Herglotz source can vanish.  This closes the differential-linear layer of the facet-sewn source.
It does not assert nonlinear differential-algebraic independence.
-/

open Complex Set Filter Finset
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The one-pole-deleted tail is analytic at the deleted pole. -/
theorem analyticAt_primeLogTail
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (p₀ : Nat.Primes) :
    AnalyticAt ℂ (primeLogTail u p₀) (primeLogSupport p₀ : ℂ) := by
  let S : Set Nat.Primes := {q | q ∉ ({p₀} : Finset Nat.Primes)}
  have hsum := summableLocallyUniformlyOn_primeLogHerglotz_on_off_poles S u C hu
  have hdiff : DifferentiableOn ℂ (primeLogTail u p₀) (primeLogPoleSetOn S)ᶜ := by
    apply SummableLocallyUniformlyOn.differentiableOn
      (isOpen_compl_primeLogPoleSetOn S) hsum
    intro q z hz
    have hne : (primeLogSupport q : ℂ) - z ≠ 0 := by
      intro h
      apply hz
      exact ⟨q, sub_eq_zero.mp h⟩
    exact (((differentiableAt_const (c := (primeLogSupport q : ℂ))).sub
      differentiableAt_id).inv hne).const_mul _
  exact hdiff.analyticAt ((isOpen_compl_primeLogPoleSetOn S).mem_nhds
    (primeLogCenter_notMem_otherPoleSet p₀))

/-- The totalized prime-log source is meromorphic at each declared pole. -/
theorem meromorphicAt_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (p₀ : Nat.Primes) :
    MeromorphicAt (primeLogHerglotz u) (primeLogSupport p₀ : ℂ) := by
  let a : ℂ := primeLogSupport p₀
  let w : ℂ := primeDyadicWeight u p₀
  have htail := analyticAt_primeLogTail u C hu p₀
  have hpolar : MeromorphicAt (fun z : ℂ => w * (z - a)⁻¹) a := by
    fun_prop
  have heq : primeLogHerglotz u = fun z => primeLogTail u p₀ z - w * (z - a)⁻¹ := by
    funext z
    have hsplit := primeLogHerglotz_add_polar_eq_tail u C hu p₀ z
    dsimp [a, w]
    linear_combination hsplit
  rw [heq]
  exact htail.meromorphicAt.sub hpolar

/-- Every prime logarithm has meromorphic order exactly `-1`. -/
theorem meromorphicOrderAt_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (p₀ : Nat.Primes) :
    meromorphicOrderAt (primeLogHerglotz u) (primeLogSupport p₀ : ℂ) =
      ((-1 : ℤ) : WithTop ℤ) := by
  let a : ℂ := primeLogSupport p₀
  let w : ℂ := primeDyadicWeight u p₀
  have hw : w ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (primeDyadicWeight_pos u p₀))
  have htail := analyticAt_primeLogTail u C hu p₀
  let polar : ℂ → ℂ := fun z => -w * (z - a)⁻¹
  have hpolarOrder : meromorphicOrderAt polar a = ((-1 : ℤ) : WithTop ℤ) := by
    have hconst : AnalyticAt ℂ (fun _ : ℂ => -w) a := analyticAt_const
    change meromorphicOrderAt ((fun _ : ℂ => -w) * (fun z : ℂ => (z - a)⁻¹)) a = _
    rw [meromorphicOrderAt_mul_of_ne_zero hconst (neg_ne_zero.mpr hw)]
    change meromorphicOrderAt ((fun z : ℂ => z - a)⁻¹) a = _
    rw [meromorphicOrderAt_inv, meromorphicOrderAt_id_sub_const]
    rfl
  have hlt : meromorphicOrderAt polar a < meromorphicOrderAt (primeLogTail u p₀) a := by
    rw [hpolarOrder]
    exact lt_of_lt_of_le (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      htail.meromorphicOrderAt_nonneg
  have heq : primeLogHerglotz u = polar + primeLogTail u p₀ := by
    funext z
    have hsplit := primeLogHerglotz_add_polar_eq_tail u C hu p₀ z
    dsimp [polar, a, w]
    linear_combination hsplit
  rw [heq, meromorphicOrderAt_add_eq_left_of_lt htail.meromorphicAt hlt, hpolarOrder]

/-- Prime-log Herglotz source translated in its argument. -/
def primeLogTranslate (u : Nat.Primes → ℝ) (h : ℂ) (z : ℂ) : ℂ :=
  primeLogHerglotz u (z + h)

theorem analyticAt_primeLogHerglotz_of_notMem
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) {z : ℂ}
    (hz : z ∈ primeLogPoleSetᶜ) :
    AnalyticAt ℂ (primeLogHerglotz u) z :=
  (differentiableOn_primeLogHerglotz_off_poles u C hu).analyticAt
    (isOpen_compl_primeLogPoleSet.mem_nhds hz)

theorem meromorphicAt_primeLogTranslate
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (h : ℂ) (p : Nat.Primes) :
    MeromorphicAt (primeLogTranslate u h) ((primeLogSupport p : ℂ) - h) := by
  let a : ℂ := (primeLogSupport p : ℂ) - h
  let g : ℂ → ℂ := fun z => z + h
  have hg : AnalyticAt ℂ g a := by fun_prop
  have hg' : deriv g a ≠ 0 := by
    dsimp [g]
    rw [deriv_add_const, deriv_id'']
    norm_num
  change MeromorphicAt (primeLogHerglotz u ∘ g) a
  apply (meromorphicAt_comp_iff_of_deriv_ne_zero hg hg').2
  simpa [a, g] using meromorphicAt_primeLogHerglotz u C hu p

theorem meromorphicOrderAt_primeLogTranslate
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (h : ℂ) (p : Nat.Primes) :
    meromorphicOrderAt (primeLogTranslate u h) ((primeLogSupport p : ℂ) - h) =
      ((-1 : ℤ) : WithTop ℤ) := by
  let a : ℂ := (primeLogSupport p : ℂ) - h
  let g : ℂ → ℂ := fun z => z + h
  have hg : AnalyticAt ℂ g a := by fun_prop
  have hg' : deriv g a ≠ 0 := by
    dsimp [g]
    rw [deriv_add_const, deriv_id'']
    norm_num
  change meromorphicOrderAt (primeLogHerglotz u ∘ g) a = _
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']
  simpa [a, g] using meromorphicOrderAt_primeLogHerglotz u C hu p

theorem analyticAt_primeLogTranslate_of_private
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    {h k : ℂ} {p : Nat.Primes}
    (hprivate : ∀ q : Nat.Primes,
      (primeLogSupport p : ℂ) - h ≠ (primeLogSupport q : ℂ) - k) :
    AnalyticAt ℂ (primeLogTranslate u k) ((primeLogSupport p : ℂ) - h) := by
  let a : ℂ := (primeLogSupport p : ℂ) - h
  have hoff : a + k ∈ primeLogPoleSetᶜ := by
    rw [Set.mem_compl_iff]
    rintro ⟨q, hq⟩
    apply hprivate q
    change (primeLogSupport q : ℂ) =
      ((primeLogSupport p : ℂ) - h) + k at hq
    rw [hq]
    ring
  have hsource := analyticAt_primeLogHerglotz_of_notMem u C hu hoff
  have hinner : AnalyticAt ℂ (fun z : ℂ => z + k) a := by fun_prop
  change AnalyticAt ℂ (primeLogHerglotz u ∘ fun z : ℂ => z + k) a
  exact AnalyticAt.comp (x := a) (g := primeLogHerglotz u)
    (f := fun z : ℂ => z + k) hsource hinner

/-- Every nontrivial finite constant-coefficient differential combination of distinct complex
translates of the prime-log source is nonzero. -/
theorem finite_primeLogTranslate_differentialCombination_ne_zero
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (H : Finset ℂ) (L : ℂ → Polynomial ℂ) {h₀ : ℂ}
    (hh₀ : h₀ ∈ H) (hL : L h₀ ≠ 0) :
    (∑ h ∈ H, constantCoeffDifferentialOperator (L h) (primeLogTranslate u h)) ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := (infinite_primeLogComplex_privatePrimes H h₀).nonempty
  have hpBad : p ∉ primeLogComplexBadPrimes H h₀ := hp
  let a : ℂ := (primeLogSupport p : ℂ) - h₀
  let term : ℂ → ℂ → ℂ := fun h =>
    constantCoeffDifferentialOperator (L h) (primeLogTranslate u h)
  have hmainMero : MeromorphicAt (primeLogTranslate u h₀) a := by
    simpa [a] using meromorphicAt_primeLogTranslate u C hu h₀ p
  have hmainOrder : meromorphicOrderAt (term h₀) a =
      ((-((L h₀).natDegree + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    exact meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole hL hmainMero
      (by simpa [a] using meromorphicOrderAt_primeLogTranslate u C hu h₀ p)
  have hother : ∀ k ∈ H.erase h₀, AnalyticAt ℂ (term k) a := by
    intro k hk
    have hkH : k ∈ H := (Finset.mem_erase.mp hk).2
    have hkh₀ : k ≠ h₀ := (Finset.mem_erase.mp hk).1
    have hprivate := primeLogComplex_private_of_notMem_bad H h₀ hpBad k hkH hkh₀
    apply analyticAt_constantCoeffDifferentialOperator
    exact analyticAt_primeLogTranslate_of_private u C hu hprivate
  have hrest : AnalyticAt ℂ (∑ k ∈ H.erase h₀, term k) a := by
    exact Finset.analyticAt_sum _ fun k hk => hother k hk
  have hlt : meromorphicOrderAt (term h₀) a <
      meromorphicOrderAt (∑ k ∈ H.erase h₀, term k) a := by
    rw [hmainOrder]
    apply lt_of_lt_of_le _ hrest.meromorphicOrderAt_nonneg
    exact_mod_cast (show (-((L h₀).natDegree + 1 : ℕ) : ℤ) < 0 by omega)
  have hsplit : (∑ h ∈ H, term h) =
      term h₀ + ∑ h ∈ H.erase h₀, term h := by
    rw [← Finset.sum_erase_add _ _ hh₀, add_comm]
  intro hzero
  have hord := congrArg (fun f : ℂ → ℂ => meromorphicOrderAt f a) hzero
  change meromorphicOrderAt (∑ h ∈ H, term h) a = meromorphicOrderAt 0 a at hord
  rw [hsplit, meromorphicOrderAt_add_eq_left_of_lt hrest.meromorphicAt hlt,
    hmainOrder] at hord
  simp at hord

end

end GaloisForLFunctions.HTGeometry
