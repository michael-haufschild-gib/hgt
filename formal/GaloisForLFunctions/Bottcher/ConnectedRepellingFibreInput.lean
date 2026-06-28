/-
# Connected-case Böttcher transcendence from a repelling separable fibre

This focused hRigid brick removes the strongest artificial datum from the
absolute repelling input: the callback no longer has to choose a fibre root
already fixed by `w ↦ w^(2^p)` or prove its simplicity.  A nonzero root of a
separable fibre over a strongly repelling periodic base point is enough; the
finite root-set dynamics supplies a periodic fibre root internally.
-/
import GaloisForLFunctions.Bottcher.ConnectedTranscendence
import GaloisForLFunctions.Bottcher.RelativeFibreGeneric
import GaloisForLFunctions.U0.HolomorphicIFT

open Polynomial Filter Topology Set Metric

namespace Bottcher

/-- A strong multiplier bound survives replacing the period `p` by `p*m`. -/
theorem strong_repelling_norm_pow {lam : ℂ} {p m : ℕ} (hm : 1 ≤ m)
    (h : (2 ^ p : ℝ) < ‖lam‖) :
    (2 ^ (p * m) : ℝ) < ‖lam ^ m‖ := by
  rw [norm_pow]
  have hm0 : m ≠ 0 := by omega
  have hpow : (2 ^ p : ℝ) ^ m < ‖lam‖ ^ m :=
    pow_lt_pow_left₀ h (pow_nonneg (by norm_num) p) hm0
  simpa [pow_mul] using hpow

/-- A positive-degree complex polynomial whose constant term is nonzero has a nonzero root. -/
theorem exists_nonzero_root_of_natDegree_pos_eval_zero_ne {q : Polynomial ℂ}
    (hdeg : 0 < q.natDegree) (h0 : q.eval 0 ≠ 0) :
    ∃ w : ℂ, q.eval w = 0 ∧ w ≠ 0 := by
  have hdegpos : 0 < q.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdeg
  obtain ⟨w, hw⟩ := Complex.exists_root hdegpos
  refine ⟨w, hw, ?_⟩
  intro hw0
  subst w
  exact h0 hw

/-- A minimal vanishing relation has nonzero constant coefficient in the fibre variable. -/
theorem minimal_relation_coeff_zero_ne {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0) (hdeg : 1 ≤ P.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree) :
    P.coeff 0 ≠ 0 := by
  have hndvd := factor_not_dvd_of_minimal hUo hUc hUne c hU P hP0 hdeg hPrel hPmin (0 : ℂ)
  intro hcoeff
  apply hndvd
  have hx : (Polynomial.X : Polynomial (Polynomial ℂ)) ∣ P := by
    rw [Polynomial.X_dvd_iff]
    exact hcoeff
  simpa using hx

/-- **Absolute connected `φ_c`-transcendence from a repelling separable fibre.**

Compared with `phiMero_transcendental_of_repelling_input`, the dynamical
callback no longer supplies a simple root `w₀` satisfying
`w₀ ^ (2 ^ p) = w₀`.  It supplies only:

* a strongly repelling periodic base point `z₀`,
* denominator avoidance for the divisibility gateway,
* a nonzero root of the fibre `P(z₀, W)`,
* separability and nontriviality of that fibre.

The proof clears denominators, uses `exists_pow_fixed_root` on the finite
nonzero root set, and then recovers the simple-root derivative from
separability. -/
theorem phiMero_transcendental_of_repelling_separable_fibre_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam z₀ w : ℂ),
          (quadratic c)^[p] z₀ = z₀ ∧
          HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
          (2 ^ p : ℝ) < ‖lam‖ ∧
          (∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            e.eval z₀ ≠ 0) ∧
          (P.map (Polynomial.evalRingHom z₀)).Separable ∧
          P.map (Polynomial.evalRingHom z₀) ≠ 0 ∧
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i = 0) ∧
          w ≠ 0) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  obtain ⟨p, lam, z₀, w, hFz, hlam, hnorm, havoid, hsep, hPz0, hrootw, hwne⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount
  have hesc := relation_vanishes_escapeOpen hUo hUne c hU P hPrel
  have hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
      ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
    intro z hz
    rw [compRelPoly_relation]
    exact relation_iterate_eq_zero P p hesc z (hU hz)
  obtain ⟨e, S, he0, hPS⟩ :=
    divides_relation_up_to_denom c P (compRelPoly c p P) hP0 hPmin hPrel hQrel
  have hez : e.eval z₀ ≠ 0 := havoid e S he0 hPS
  obtain ⟨w₀, m, hm1, hw0ne, hroot0, hwfix⟩ :=
    exists_pow_fixed_root c p P S hFz hPS hez hPz0 hrootw hwne
  have hrootMap : (P.map (Polynomial.evalRingHom z₀)).eval w₀ = 0 := by
    rw [← relation_eq_eval_map P z₀ w₀]
    exact hroot0
  have hd : (P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀ ≠ 0 :=
    eval_derivative_ne_zero_of_separable hsep hrootMap
  refine ⟨p * m, lam ^ m, w₀,
    (P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀, z₀,
    hroot0, relation_hasDerivAt_w P z₀ w₀, hd, ?_, ?_, hwfix, hw0ne, ?_⟩
  · rw [Function.iterate_mul]
    exact Function.iterate_fixed hFz m
  · exact hasDerivAt_iterate_periodic (F := quadratic c) hFz hlam m
  · exact strong_repelling_norm_pow hm1 hnorm

/-- **Absolute connected `φ_c`-transcendence from a full separable repelling fibre.**

This removes one more artificial terminal datum from
`phiMero_transcendental_of_repelling_separable_fibre_input`: the callback no longer chooses a nonzero
root of the fibre.  It only proves that the specialized fibre keeps full positive degree and has
nonzero constant term; the fundamental theorem of algebra then supplies a nonzero root. -/
theorem phiMero_transcendental_of_repelling_full_separable_fibre_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam z₀ : ℂ),
          (quadratic c)^[p] z₀ = z₀ ∧
          HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
          (2 ^ p : ℝ) < ‖lam‖ ∧
          (∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            e.eval z₀ ≠ 0) ∧
          (P.map (Polynomial.evalRingHom z₀)).Separable ∧
          (P.map (Polynomial.evalRingHom z₀)).natDegree = P.natDegree ∧
          (P.map (Polynomial.evalRingHom z₀)).eval 0 ≠ 0) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_separable_fibre_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  obtain ⟨p, lam, z₀, hFz, hlam, hnorm, havoid, hsep, hfibdeg, hfib0⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount
  set q : Polynomial ℂ := P.map (Polynomial.evalRingHom z₀) with hqdef
  have hqnat : 0 < q.natDegree := by
    rw [hqdef, hfibdeg]
    exact hdeg
  obtain ⟨w, hroot, hwne⟩ := exists_nonzero_root_of_natDegree_pos_eval_zero_ne hqnat (by
    rwa [hqdef])
  have hqne' : q ≠ 0 := by
    intro hzero
    rw [hzero] at hfib0
    simp at hfib0
  have hqne : P.map (Polynomial.evalRingHom z₀) ≠ 0 := by
    rwa [← hqdef]
  refine ⟨p, lam, z₀, w, hFz, hlam, hnorm, havoid, hsep, hqne, ?_, hwne⟩
  rw [relation_eq_eval_map, ← hqdef]
  exact hroot

/-- **Absolute connected `φ_c`-transcendence from coefficient-level bad-locus avoidance.**

This is the coefficient-level form of
`phiMero_transcendental_of_repelling_full_separable_fibre_input`: instead of asking the callback for
full fibre degree and nonzero fibre constant term, it asks only that the selected periodic point avoid
the zero loci of `P.coeff P.natDegree` and `P.coeff 0`.  The former gives full fibre degree by
`fiber_natDegree_eq`; the latter is the fibre constant term.  Minimality proves `P.coeff 0 ≠ 0`, so
this is now an explicit finite algebraic bad locus. -/
theorem phiMero_transcendental_of_repelling_coeff_avoidance_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ (p : ℕ) (lam z₀ : ℂ),
          (quadratic c)^[p] z₀ = z₀ ∧
          HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
          (2 ^ p : ℝ) < ‖lam‖ ∧
          (∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
            (Polynomial.C e) * (compRelPoly c p P) = P * S →
            e.eval z₀ ≠ 0) ∧
          (P.map (Polynomial.evalRingHom z₀)).Separable ∧
          (P.coeff P.natDegree).eval z₀ ≠ 0 ∧
          (P.coeff 0).eval z₀ ≠ 0) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_full_separable_fibre_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  have hconst_poly : P.coeff 0 ≠ 0 :=
    minimal_relation_coeff_zero_ne hUo hUc hUne c hU P hP0 hdeg hPrel hPmin
  obtain ⟨p, lam, z₀, hFz, hlam, hnorm, havoid, hsep, hlead, hconst⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, lam, z₀, hFz, hlam, hnorm, havoid, hsep, fiber_natDegree_eq hlead, ?_⟩
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simpa using hconst

/-- **Absolute connected `φ_c`-transcendence with a selected denominator.**

The denominator-clearing step produces one concrete denominator `e` after a period `p` is chosen.
This form no longer asks the dynamical callback for a single periodic point avoiding *every*
denominator compatible with `p`; it asks for a period `p` such that, for each selected denominator
identity, a strongly repelling periodic point can be chosen avoiding that denominator and the remaining
coefficient/separability bad loci. -/
theorem phiMero_transcendental_of_repelling_selected_denominator_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
          (Polynomial.C e) * (compRelPoly c p P) = P * S →
          ∃ (lam z₀ : ℂ),
            (quadratic c)^[p] z₀ = z₀ ∧
            HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
            (2 ^ p : ℝ) < ‖lam‖ ∧
            e.eval z₀ ≠ 0 ∧
            (P.map (Polynomial.evalRingHom z₀)).Separable ∧
            (P.coeff P.natDegree).eval z₀ ≠ 0 ∧
            (P.coeff 0).eval z₀ ≠ 0) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  have hconst_poly : P.coeff 0 ≠ 0 :=
    minimal_relation_coeff_zero_ne hUo hUc hUne c hU P hP0 hdeg hPrel hPmin
  obtain ⟨p, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  have hesc := relation_vanishes_escapeOpen hUo hUne c hU P hPrel
  have hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
      ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
    intro z hz
    rw [compRelPoly_relation]
    exact relation_iterate_eq_zero P p hesc z (hU hz)
  obtain ⟨e, S, he0, hPS⟩ :=
    divides_relation_up_to_denom c P (compRelPoly c p P) hP0 hPmin hPrel hQrel
  obtain ⟨lam, z₀, hFz, hlam, hnorm, hez, hsep, hlead, hconst⟩ :=
    hpinput e S he0 hPS
  set q : Polynomial ℂ := P.map (Polynomial.evalRingHom z₀) with hqdef
  have hqnat : 0 < q.natDegree := by
    rw [hqdef, fiber_natDegree_eq hlead]
    exact hdeg
  obtain ⟨w, hrootq, hwne⟩ := exists_nonzero_root_of_natDegree_pos_eval_zero_ne hqnat (by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa [hqdef] using hconst)
  have hqne' : q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hqnat
    omega
  have hqne : P.map (Polynomial.evalRingHom z₀) ≠ 0 := by
    rwa [← hqdef]
  have hrootw : ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i = 0 := by
    rw [relation_eq_eval_map, ← hqdef]
    exact hrootq
  obtain ⟨w₀, m, hm1, hw0ne, hroot0, hwfix⟩ :=
    exists_pow_fixed_root c p P S hFz hPS hez hqne hrootw hwne
  have hrootMap : (P.map (Polynomial.evalRingHom z₀)).eval w₀ = 0 := by
    rw [← relation_eq_eval_map P z₀ w₀]
    exact hroot0
  have hd : (P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀ ≠ 0 :=
    eval_derivative_ne_zero_of_separable hsep hrootMap
  refine ⟨p * m, lam ^ m, w₀,
    (P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀, z₀,
    hroot0, relation_hasDerivAt_w P z₀ w₀, hd, ?_, ?_, hwfix, hw0ne, ?_⟩
  · rw [Function.iterate_mul]
    exact Function.iterate_fixed hFz m
  · exact hasDerivAt_iterate_periodic (F := quadratic c) hFz hlam m
  · exact strong_repelling_norm_pow hm1 hnorm

/-- **Denominator clearing for the composed relation.**

For any chosen period `p`, minimality of `P` creates a concrete denominator-clearing identity
`(C e) * compRelPoly c p P = P * S`.  This is the exact `e,S,hPS` datum needed by the finite-count
repelling route; callers should not provide it as a terminal hypothesis. -/
theorem exists_compRelPoly_denominator_of_minimal {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (p : ℕ) :
    ∃ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 ∧
      (Polynomial.C e) * (compRelPoly c p P) = P * S := by
  have hesc := relation_vanishes_escapeOpen hUo hUne c hU P hPrel
  have hQrel : ∀ z ∈ U, ∑ i ∈ (compRelPoly c p P).support,
      ((compRelPoly c p P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0 := by
    intro z hz
    rw [compRelPoly_relation]
    exact relation_iterate_eq_zero P p hesc z (hU hz)
  exact divides_relation_up_to_denom c P (compRelPoly c p P) hP0 hPmin hPrel hQrel

/-- The denominator polynomial selected by `exists_compRelPoly_denominator_of_minimal`. -/
noncomputable def chosenCompRelDenom {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (p : ℕ) : Polynomial ℂ :=
  Classical.choose (exists_compRelPoly_denominator_of_minimal hUo hUne c hU P hP0 hPrel hPmin p)

/-- The quotient polynomial paired with `chosenCompRelDenom`. -/
noncomputable def chosenCompRelQuot {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (p : ℕ) : Polynomial (Polynomial ℂ) :=
  Classical.choose (Classical.choose_spec
    (exists_compRelPoly_denominator_of_minimal hUo hUne c hU P hP0 hPrel hPmin p))

/-- The chosen denominator is nonzero and clears `compRelPoly`. -/
theorem chosenCompRelDenom_spec {U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree)
    (p : ℕ) :
    chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p ≠ 0 ∧
      (Polynomial.C (chosenCompRelDenom hUo hUne c hU P hP0 hPrel hPmin p)) *
          (compRelPoly c p P) =
        P * chosenCompRelQuot hUo hUne c hU P hP0 hPrel hPmin p := by
  dsimp [chosenCompRelDenom, chosenCompRelQuot]
  exact Classical.choose_spec (Classical.choose_spec
    (exists_compRelPoly_denominator_of_minimal hUo hUne c hU P hP0 hPrel hPmin p))

/-- **Absolute connected `φ_c`-transcendence from one chosen denominator.**

This is the denominator-order correction for the finite-count hRigid lane.  The older
`phiMero_transcendental_of_repelling_selected_denominator_input` asks the callback to work for every
denominator identity after a period is fixed.  That is too strong for finite-root avoidance, since a
valid denominator identity can be multiplied by an arbitrary polynomial.  This form lets the callback
choose the period and one denominator-clearing identity together; the proof then uses exactly that
identity in the existing finite-fibre argument. -/
theorem phiMero_transcendental_of_repelling_chosen_denominator_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ (p : ℕ) (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)) (lam z₀ : ℂ),
          e ≠ 0 ∧
          (Polynomial.C e) * (compRelPoly c p P) = P * S ∧
          (quadratic c)^[p] z₀ = z₀ ∧
          HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
          (2 ^ p : ℝ) < ‖lam‖ ∧
          e.eval z₀ ≠ 0 ∧
          (P.map (Polynomial.evalRingHom z₀)).Separable ∧
          (P.coeff P.natDegree).eval z₀ ≠ 0 ∧
          (P.coeff 0).eval z₀ ≠ 0) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount
  have hconst_poly : P.coeff 0 ≠ 0 :=
    minimal_relation_coeff_zero_ne hUo hUc hUne c hU P hP0 hdeg hPrel hPmin
  obtain ⟨p, e, S, lam, z₀, he0, hPS, hFz, hlam, hnorm, hez, hsep, hlead, hconst⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  set q : Polynomial ℂ := P.map (Polynomial.evalRingHom z₀) with hqdef
  have hqnat : 0 < q.natDegree := by
    rw [hqdef, fiber_natDegree_eq hlead]
    exact hdeg
  obtain ⟨w, hrootq, hwne⟩ := exists_nonzero_root_of_natDegree_pos_eval_zero_ne hqnat (by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa [hqdef] using hconst)
  have hqne' : q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hqnat
    omega
  have hqne : P.map (Polynomial.evalRingHom z₀) ≠ 0 := by
    rwa [← hqdef]
  have hrootw : ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i = 0 := by
    rw [relation_eq_eval_map, ← hqdef]
    exact hrootq
  obtain ⟨w₀, m, hm1, hw0ne, hroot0, hwfix⟩ :=
    exists_pow_fixed_root c p P S hFz hPS hez hqne hrootw hwne
  have hrootMap : (P.map (Polynomial.evalRingHom z₀)).eval w₀ = 0 := by
    rw [← relation_eq_eval_map P z₀ w₀]
    exact hroot0
  have hd : (P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀ ≠ 0 :=
    eval_derivative_ne_zero_of_separable hsep hrootMap
  refine ⟨p * m, lam ^ m, w₀,
    (P.map (Polynomial.evalRingHom z₀)).derivative.eval w₀, z₀,
    hroot0, relation_hasDerivAt_w P z₀ w₀, hd, ?_, ?_, hwfix, hw0ne, ?_⟩
  · rw [Function.iterate_mul]
    exact Function.iterate_fixed hFz m
  · exact hasDerivAt_iterate_periodic (F := quadratic c) hFz hlam m
  · exact strong_repelling_norm_pow hm1 hnorm

/-- The sparse fibre over the actual support of an absolute relation is its specialization. -/
theorem abs_fibrePoly_eq_map_eval (P : Polynomial (Polynomial ℂ)) (z : ℂ) :
    fibrePoly (fun i z => (P.coeff i).eval z) P.support z =
      P.map (Polynomial.evalRingHom z) := by
  ext j
  rw [coeff_fibrePoly, Polynomial.coeff_map]
  by_cases hj : j ∈ P.support
  · simp [hj]
  · have hc : P.coeff j = 0 := Polynomial.notMem_support_iff.mp hj
    simp [hj, hc]

/-- **Absolute connected `φ_c`-transcendence from selected-denominator sparse crossing.**

This is the crossing form of `phiMero_transcendental_of_repelling_selected_denominator_input`.
After denominator clearing has selected `e`, the callback supplies an accumulating set of strongly
repelling periodic targets avoiding only `e` and the constant coefficient.  The sparse resultant
crossing lemma chooses one target where the absolute fibre is separable and keeps full degree. -/
theorem phiMero_transcendental_of_repelling_selected_denominator_crossing_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
          (Polynomial.C e) * (compRelPoly c p P) = P * S →
          ∃ (Ω : Set ℂ) (w z₁ : ℂ) (T : Set ℂ),
            IsPreconnected Ω ∧
            w ∈ Ω ∧
            (P.coeff P.natDegree).eval w ≠ 0 ∧
            (P.map (Polynomial.evalRingHom w)).Separable ∧
            z₁ ∈ Ω ∧
            (∃ᶠ z in 𝓝[≠] z₁, z ∈ T) ∧
            (∀ z₀ ∈ T, ∃ lam : ℂ,
              (quadratic c)^[p] z₀ = z₀ ∧
              HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
              (2 ^ p : ℝ) < ‖lam‖ ∧
              e.eval z₀ ≠ 0 ∧
              (P.coeff 0).eval z₀ ≠ 0)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_selected_denominator_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, ?_⟩
  intro e S he0 hPS
  obtain ⟨Ω, w, z₁, T, hΩc, hw, hleadw, hsepw, hz₁, haccum, hgeom⟩ :=
    hpinput e S he0 hPS
  let a : ℕ → ℂ → ℂ := fun i z => (P.coeff i).eval z
  have hsupp : P.support ⊆ Finset.range (P.natDegree + 1) := by
    intro i hi
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)))
  have hN : P.natDegree ∈ P.support := by
    exact Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP0)
  have ha : ∀ i ∈ P.support, AnalyticOnNhd ℂ (a i) Ω := by
    intro i _hi
    exact analyticOnNhd_polyEval Ω (P.coeff i)
  have hleadw_fib : a P.natDegree w ≠ 0 := by
    simpa [a] using hleadw
  have hsepw_fib : (fibrePoly a P.support w).Separable := by
    have hfibw : fibrePoly a P.support w = P.map (Polynomial.evalRingHom w) := by
      simpa [a] using abs_fibrePoly_eq_map_eval P w
    rwa [hfibw]
  obtain ⟨z₀, hz₀T, hlead₀_fib, hsep₀_fib⟩ :=
    exists_sparse_fibre_separable_crossing (a := a) (s := P.support) (N := P.natDegree)
      hdeg hsupp hN hΩc ha hw hleadw_fib hsepw_fib hz₁ haccum
  obtain ⟨lam, hFz, hlam, hnorm, hez, hconst⟩ := hgeom z₀ hz₀T
  have hsep₀ : (P.map (Polynomial.evalRingHom z₀)).Separable := by
    have hfib₀ : fibrePoly a P.support z₀ = P.map (Polynomial.evalRingHom z₀) := by
      simpa [a] using abs_fibrePoly_eq_map_eval P z₀
    rwa [hfib₀] at hsep₀_fib
  have hlead₀ : (P.coeff P.natDegree).eval z₀ ≠ 0 := by
    simpa [a] using hlead₀_fib
  exact ⟨lam, z₀, hFz, hlam, hnorm, hez, hsep₀, hlead₀, hconst⟩

/-- A function-field-separable absolute relation has a full-degree separable specialization. -/
theorem exists_abs_full_separable_specialization_of_fraction_separable
    (P : Polynomial (Polynomial ℂ))
    (hsep : (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable)
    (hdeg : 1 ≤ P.natDegree) :
    ∃ w : ℂ, (P.coeff P.natDegree).eval w ≠ 0 ∧
      (P.map (Polynomial.evalRingHom w)).Separable := by
  obtain ⟨w, _hwcircle, hlead, hsepw⟩ :=
    HolomorphicIFT.exists_squarefree_specialization hsep hdeg
  exact ⟨w, hlead, hsepw⟩

/-- A minimal vanishing relation is irreducible over the function field `ℂ(z)`. -/
theorem minimal_relation_irreducible_fraction_field {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0) (hdeg : 1 ≤ P.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree) :
    Irreducible (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))) := by
  classical
  set alg := algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) with halg
  have halginj : Function.Injective alg := IsFractionRing.injective _ _
  set Pf := P.map alg with hPf
  have hPfdeg : Pf.natDegree = P.natDegree := natDegree_map_eq_of_injective halginj P
  have hPf0 : Pf ≠ 0 := fun h => hP0 ((Polynomial.map_eq_zero_iff halginj).mp (by
    simpa [Pf] using h))
  have hPf_nu : ¬ IsUnit Pf := fun hu => by
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hPfdeg] at h0
    omega
  refine (irreducible_or_factor hPf_nu).resolve_right ?_
  rintro ⟨A, B, hAnu, hBnu, hPfAB⟩
  have hA0 : A ≠ 0 := by rintro rfl; rw [zero_mul] at hPfAB; exact hPf0 hPfAB
  have hB0 : B ≠ 0 := by rintro rfl; rw [mul_zero] at hPfAB; exact hPf0 hPfAB
  obtain ⟨bA, hbAmem, hbA⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial ℂ)) A
  obtain ⟨bB, hbBmem, hbB⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial ℂ)) B
  set Atil := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial ℂ)) A with hAtil
  set Btil := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial ℂ)) B with hBtil
  have hbApoly0 : bA ≠ 0 := nonZeroDivisors.ne_zero hbAmem
  have hbBpoly0 : bB ≠ 0 := nonZeroDivisors.ne_zero hbBmem
  have hbA0 : alg bA ≠ 0 := fun h => hbApoly0 (halginj (by rw [h, map_zero]))
  have hbB0 : alg bB ≠ 0 := fun h => hbBpoly0 (halginj (by rw [h, map_zero]))
  have hAtil0 : Atil ≠ 0 := fun h => hA0
    ((IsFractionRing.integerNormalization_eq_zero_iff).mp (by rw [← hAtil, h]))
  have hBtil0 : Btil ≠ 0 := fun h => hB0
    ((IsFractionRing.integerNormalization_eq_zero_iff).mp (by rw [← hBtil, h]))
  have hdegA : 1 ≤ A.natDegree := by
    rcases Nat.eq_zero_or_pos A.natDegree with h | h
    · exfalso
      apply hAnu
      rw [Polynomial.eq_C_of_natDegree_eq_zero h]
      refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
      intro hc
      apply hA0
      rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc, map_zero]
    · exact h
  have hdegB : 1 ≤ B.natDegree := by
    rcases Nat.eq_zero_or_pos B.natDegree with h | h
    · exfalso
      apply hBnu
      rw [Polynomial.eq_C_of_natDegree_eq_zero h]
      refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
      intro hc
      apply hB0
      rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc, map_zero]
    · exact h
  have hsmul : ∀ (r : Polynomial ℂ) (p : (FractionRing (Polynomial ℂ))[X]),
      r • p = C (alg r) * p := fun r p => by
    rw [← algebraMap_smul (FractionRing (Polynomial ℂ)) r p, Polynomial.smul_eq_C_mul]
  have hdegAtil : Atil.natDegree = A.natDegree := by
    have h1 := natDegree_map_eq_of_injective halginj Atil
    rw [hbA, hsmul, Polynomial.natDegree_C_mul hbA0] at h1
    omega
  have hdegBtil : Btil.natDegree = B.natDegree := by
    have h1 := natDegree_map_eq_of_injective halginj Btil
    rw [hbB, hsmul, Polynomial.natDegree_C_mul hbB0] at h1
    omega
  have hdescent : Atil * Btil = C (bA * bB) * P := by
    apply Polynomial.map_injective alg halginj
    rw [Polynomial.map_mul, hbA, hbB, hsmul, hsmul, Polynomial.map_mul, Polynomial.map_C,
      map_mul alg, Polynomial.C_mul, ← hPf, hPfAB]
    ring
  have hdegsum : Atil.natDegree + Btil.natDegree = P.natDegree := by
    have hm := Polynomial.natDegree_mul hAtil0 hBtil0
    rw [hdescent, Polynomial.natDegree_C_mul (mul_ne_zero hbApoly0 hbBpoly0)] at hm
    exact hm.symm
  let fA : ℂ → ℂ := fun z =>
    ∑ i ∈ Atil.support, (Atil.coeff i).aeval z * (bottcherCoord c z) ^ i
  let fB : ℂ → ℂ := fun z =>
    ∑ i ∈ Btil.support, (Btil.coeff i).aeval z * (bottcherCoord c z) ^ i
  have hfA : AnalyticOnNhd ℂ fA U := by
    have h := analyticOnNhd_eval₂_bottcher c hU Atil
    have hfe : (fun z => Atil.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) = fA := by
      funext z
      dsimp [fA]
      rw [eval₂_eq_relation]
      simp [Polynomial.coe_aeval_eq_eval]
    rwa [hfe] at h
  have hfB : AnalyticOnNhd ℂ fB U := by
    have h := analyticOnNhd_eval₂_bottcher c hU Btil
    have hfe : (fun z => Btil.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) = fB := by
      funext z
      dsimp [fB]
      rw [eval₂_eq_relation]
      simp [Polynomial.coe_aeval_eq_eval]
    rwa [hfe] at h
  have hprod : EqOn (fun z => fA z * fB z) 0 U := by
    intro z hz
    have hmul := relation_mul Atil Btil z (bottcherCoord c z)
    rw [hdescent, relation_mul, relation_C, hPrel z hz, mul_zero] at hmul
    exact hmul.symm
  rcases analyticOnNhd_domain hfA hfB hUc hUo hprod with hAz | hBz
  · have hminA := hPmin Atil hAtil0 (by intro z hz; exact hAz hz)
    have hltA : Atil.natDegree < P.natDegree := by
      rw [← hdegsum]
      omega
    omega
  · have hminB := hPmin Btil hBtil0 (by intro z hz; exact hBz hz)
    have hltB : Btil.natDegree < P.natDegree := by
      rw [← hdegsum]
      omega
    omega

/-- A minimal vanishing relation is separable over the function field `ℂ(z)`. -/
theorem minimal_relation_fraction_field_separable {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0) (hdeg : 1 ≤ P.natDegree)
    (hPrel : ∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
    (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
        (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        P.natDegree ≤ R.natDegree) :
    (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable :=
  (minimal_relation_irreducible_fraction_field hUo hUc c hU P hP0 hdeg hPrel hPmin).separable

/-- **Absolute connected `φ_c`-transcendence from function-field separability plus target crossing.**

This removes the witness specialization from
`phiMero_transcendental_of_repelling_selected_denominator_crossing_input`.  Once the minimal relation
is known to be separable over `ℂ(z)`, `exists_abs_full_separable_specialization_of_fraction_separable`
creates the full-degree squarefree seed used by sparse crossing.  The callback only supplies the
selected denominator's accumulating strongly-repelling target set. -/
theorem phiMero_transcendental_of_repelling_fraction_separable_crossing_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
          (Polynomial.C e) * (compRelPoly c p P) = P * S →
          ∃ (z₁ : ℂ) (T : Set ℂ),
            (∃ᶠ z in 𝓝[≠] z₁, z ∈ T) ∧
            (∀ z₀ ∈ T, ∃ lam : ℂ,
              (quadratic c)^[p] z₀ = z₀ ∧
              HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
              (2 ^ p : ℝ) < ‖lam‖ ∧
              e.eval z₀ ≠ 0 ∧
              (P.coeff 0).eval z₀ ≠ 0)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_selected_denominator_crossing_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  have hsepFrac : (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable :=
    minimal_relation_fraction_field_separable hUo hUc c hU P hP0 hdeg hPrel hPmin
  obtain ⟨w, hleadw, hsepw⟩ :=
    exists_abs_full_separable_specialization_of_fraction_separable P hsepFrac hdeg
  obtain ⟨p, hpinput⟩ :=
    hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, ?_⟩
  intro e S he0 hPS
  obtain ⟨z₁, T, haccum, hgeom⟩ := hpinput e S he0 hPS
  exact ⟨univ, w, z₁, T, isPreconnected_univ, mem_univ w, hleadw, hsepw,
    mem_univ z₁, haccum, hgeom⟩

/-- A nonzero complex polynomial is eventually nonzero in every punctured neighbourhood. -/
theorem eventually_eval_ne_zero_nhdsWithin_ne_of_ne_zero (p : Polynomial ℂ) (hp : p ≠ 0)
    (z₁ : ℂ) :
    ∀ᶠ z in 𝓝[≠] z₁, p.eval z ≠ 0 := by
  classical
  have hroot_fin : {z : ℂ | p.eval z = 0}.Finite := by
    have : {z : ℂ | p.eval z = 0} = ↑p.roots.toFinset := by
      ext z
      simp only [Set.mem_setOf_eq, Multiset.mem_toFinset, mem_roots hp, IsRoot, Finset.mem_coe]
    rw [this]
    exact p.roots.toFinset.finite_toSet
  let S : Set ℂ := {z : ℂ | p.eval z = 0} \ {z₁}
  have hSfin : S.Finite := hroot_fin.subset (by intro z hz; exact hz.1)
  have hz₁S : z₁ ∉ S := by simp [S]
  have hScompl_nhds : Sᶜ ∈ 𝓝 z₁ := hSfin.isClosed.compl_mem_nhds hz₁S
  have hScompl_within : Sᶜ ∈ 𝓝[≠] z₁ := nhdsWithin_le_nhds hScompl_nhds
  filter_upwards [hScompl_within, self_mem_nhdsWithin] with z hzS hzne hzero
  exact hzS ⟨hzero, by simpa using hzne⟩

/-- An accumulating set remains accumulating after deleting the zero loci of two nonzero polynomials. -/
theorem frequently_mem_inter_nonzero_polys {z₁ : ℂ} {T : Set ℂ} {e q : Polynomial ℂ}
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ T) (he : e ≠ 0) (hq : q ≠ 0) :
    ∃ᶠ z in 𝓝[≠] z₁, z ∈ {z | z ∈ T ∧ e.eval z ≠ 0 ∧ q.eval z ≠ 0} := by
  have heevent := eventually_eval_ne_zero_nhdsWithin_ne_of_ne_zero e he z₁
  have hqevent := eventually_eval_ne_zero_nhdsWithin_ne_of_ne_zero q hq z₁
  refine ((haccum.and_eventually heevent).and_eventually hqevent).mono ?_
  intro z hz
  exact ⟨hz.1.1, hz.1.2, hz.2⟩

/-- **Absolute connected `φ_c`-transcendence from an accumulating repelling target set.**

This removes the last finite bad-locus avoidance from
`phiMero_transcendental_of_repelling_fraction_separable_crossing_input`: for a selected denominator
`e`, the callback supplies only an accumulating set of strongly repelling periodic targets.  The proof
shrinks that set away from the zero loci of `e` and `P.coeff 0`, which preserves accumulation because
both loci are finite. -/
theorem phiMero_transcendental_of_repelling_target_accumulation_input {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable →
        P.coeff 0 ≠ 0 →
        ∃ p : ℕ, ∀ (e : Polynomial ℂ) (S : Polynomial (Polynomial ℂ)), e ≠ 0 →
          (Polynomial.C e) * (compRelPoly c p P) = P * S →
          ∃ (z₁ : ℂ) (T : Set ℂ),
            (∃ᶠ z in 𝓝[≠] z₁, z ∈ T) ∧
            (∀ z₀ ∈ T, ∃ lam : ℂ,
              (quadratic c)^[p] z₀ = z₀ ∧
              HasDerivAt ((quadratic c)^[p]) lam z₀ ∧
              (2 ^ p : ℝ) < ‖lam‖)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_fraction_separable_crossing_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst_poly
  obtain ⟨p, hpinput⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst_poly
  refine ⟨p, ?_⟩
  intro e S he0 hPS
  obtain ⟨z₁, T, haccum, hgeom⟩ := hpinput e S he0 hPS
  let Tgood : Set ℂ := {z | z ∈ T ∧ e.eval z ≠ 0 ∧ (P.coeff 0).eval z ≠ 0}
  refine ⟨z₁, Tgood, ?_, ?_⟩
  · exact frequently_mem_inter_nonzero_polys haccum he0 hconst_poly
  · intro z₀ hz₀
    obtain ⟨lam, hFz, hlam, hnorm⟩ := hgeom z₀ hz₀.1
    exact ⟨lam, hFz, hlam, hnorm, hz₀.2.1, hz₀.2.2⟩

end Bottcher
