import GaloisForLFunctions.HTGeometry.CoefficientPatternDeterminant
import GaloisForLFunctions.HTGeometry.PolynomialJetEscape
import GaloisForLFunctions.HTGeometry.PrimeLogCauchyJetControllability
import GaloisForLFunctions.HTGeometry.PrimeLogGaugePerturbation
import GaloisForLFunctions.HTGeometry.DiscreteCauchyJetPacket
import GaloisForLFunctions.HTGeometry.JetFactorialScale

/-!
# Coefficient-uniform Cauchy-jet escape

The determinant polynomial turns full rank for an entire finite coefficient pattern into one
nonzero polynomial condition.  Simultaneous prime-log Cauchy-jet controllability can therefore
escape the complete rank-defect locus, not merely one preselected coefficient relation.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Reassociate a row of jet packets with the one jet packet on the combined row-node family. -/
def rowJetIndexEquiv
    (row ι : Type*) (orders : ι → ℕ) :
    (row × (Σ i, Fin (orders i))) ≃ (Σ x : row × ι, Fin (orders x.2)) where
  toFun x := ⟨(x.1, x.2.1), x.2.2⟩
  invFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  left_inv x := by rcases x with ⟨a, i, j⟩; rfl
  right_inv x := by rcases x with ⟨⟨a, i⟩, j⟩; rfl

/-- Real-linear reassociation of combined-node Cauchy jets into row-indexed jet packets. -/
def reshapeCombinedJets
    (row ι : Type*) (orders : ι → ℕ) :
    ((Σ x : row × ι, Fin (orders x.2)) → ℂ) →ₗ[ℝ]
      (row × (Σ i, Fin (orders i)) → ℂ) where
  toFun y x := y (rowJetIndexEquiv row ι orders x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem reshapeCombinedJets_surjective
    (row ι : Type*) (orders : ι → ℕ) :
    Function.Surjective (reshapeCombinedJets row ι orders) := by
  intro target
  refine ⟨fun x => target ((rowJetIndexEquiv row ι orders).symm x), ?_⟩
  funext x
  simp [reshapeCombinedJets]

/-- Prime-log Cauchy controls remain surjective after all evaluation rows are combined and
reassociated. -/
theorem reshapedPrimeLogCauchyControl_surjective
    {row ι : Type*} [Fintype row] [Fintype ι]
    [DecidableEq row] [DecidableEq ι]
    (nodes : row × ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ x, 0 < (nodes x).im) (orders : ι → ℕ) :
    Function.Surjective
      ((reshapeCombinedJets row ι orders).comp
        (cauchyJetRealLinearCombination nodes (fun x => orders x.2) primeLogSupport)) := by
  exact (reshapeCombinedJets_surjective row ι orders).comp
    (primeLogCauchyJetRealLinearCombination_surjective nodes hnodes hupper
      (fun x => orders x.2))

/-- **Coefficient-uniform positive escape.** If one target row-jet packet gives full expanded
coefficient rank, then every positive prime mass configuration and every base row-jet packet can be
perturbed at arbitrarily small positive time so that the whole coefficient pattern has full rank. -/
theorem positive_coefficientPattern_fullRank_escape
    {row ι : Type*} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    (nodes : row × ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ x, 0 < (nodes x).im) (orders : ι → ℕ)
    (base : row → ℂ) (degree : row → ℕ)
    (jetExponent : row → ((Σ i, Fin (orders i)) →₀ ℕ))
    (targetJet : row × (Σ i, Fin (orders i)) → ℂ)
    (hfullTarget : IsUnit (Matrix.of fun a b =>
      base a ^ degree b * (jetExponent b).prod (fun i e => targetJet (a, i) ^ e) :
      Matrix row row ℂ))
    (weight : Nat.Primes → ℝ) (hweight : ∀ p, 0 < weight p)
    (baseJet : row × (Σ i, Fin (orders i)) → ℂ)
    {η : ℝ} (hη : 0 < η) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε : ℝ,
      0 < ε ∧ ε < η ∧
      (∀ p, 0 < weight p + ε * a p) ∧
      IsUnit (Matrix.of fun r b =>
        base r ^ degree b * (jetExponent b).prod
          (fun i e => (baseJet + ε •
            ((reshapeCombinedJets row ι orders).comp
              (cauchyJetRealLinearCombination nodes (fun x => orders x.2)
                primeLogSupport)) a) (r, i) ^ e) :
        Matrix row row ℂ) := by
  let P := coefficientPatternDeterminant base degree jetExponent
  have hP : P ≠ 0 :=
    coefficientPatternDeterminant_ne_zero_of_isUnit
      base degree jetExponent targetJet hfullTarget
  let L := (reshapeCombinedJets row ι orders).comp
    (cauchyJetRealLinearCombination nodes (fun x => orders x.2) primeLogSupport)
  have hL : Function.Surjective L :=
    reshapedPrimeLogCauchyControl_surjective nodes hnodes hupper orders
  obtain ⟨a, ε, hε, hεη, hpos, hescape⟩ :=
    surjective_positive_control_escapes_mvPolynomial L hL weight hweight baseJet P hP hη
  refine ⟨a, ε, hε, hεη, hpos, ?_⟩
  rw [eval_coefficientPatternDeterminant] at hescape
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr hescape

/-- The coefficient-pattern full-rank escape can be performed inside every uniform neighborhood of
an arbitrary bounded prime-log gauge, with finite gauge support and exact mass reconstruction. -/
theorem coefficientPattern_fullRank_escape_in_gaugeBall
    {row ι : Type*} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι]
    (nodes : row × ι → ℂ) (hnodes : Function.Injective nodes)
    (hupper : ∀ x, 0 < (nodes x).im) (orders : ι → ℕ)
    (base : row → ℂ) (degree : row → ℕ)
    (jetExponent : row → ((Σ i, Fin (orders i)) →₀ ℕ))
    (targetJet : row × (Σ i, Fin (orders i)) → ℂ)
    (hfullTarget : IsUnit (Matrix.of fun a b =>
      base a ^ degree b * (jetExponent b).prod (fun i e => targetJet (a, i) ^ e) :
      Matrix row row ℂ))
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (baseJet : row × (Σ i, Fin (orders i)) → ℂ)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      (∀ p, primeDyadicWeight (primeLogPerturbedGauge u a ε) p =
        primeDyadicWeight u p + ε * a p) ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      IsUnit (Matrix.of fun r b =>
        base r ^ degree b * (jetExponent b).prod
          (fun i e => (baseJet + ε •
            ((reshapeCombinedJets row ι orders).comp
              (cauchyJetRealLinearCombination nodes (fun x => orders x.2)
                primeLogSupport)) a) (r, i) ^ e) :
        Matrix row row ℂ) := by
  let P := coefficientPatternDeterminant base degree jetExponent
  let L := (reshapeCombinedJets row ι orders).comp
    (cauchyJetRealLinearCombination nodes (fun x => orders x.2) primeLogSupport)
  have htarget : MvPolynomial.eval targetJet P ≠ 0 := by
    change MvPolynomial.eval targetJet
      (coefficientPatternDeterminant base degree jetExponent) ≠ 0
    rw [eval_coefficientPatternDeterminant]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hfullTarget).ne_zero
  have hL : Function.Surjective L :=
    reshapedPrimeLogCauchyControl_surjective nodes hnodes hupper orders
  obtain ⟨a, ha⟩ := hL (targetJet - baseJet)
  obtain ⟨ρ, hρ, hρη, hρpos⟩ :=
    exists_small_positive_finsupp_perturbation
      (primeDyadicWeight u) (primeDyadicWeight_pos u) a hηTime
  obtain ⟨δ, hδ, hδgauge⟩ := primeLogPerturbedGauge_uniformly_small u a hηGauge
  obtain ⟨ε, hε, hεmin, hescape⟩ :=
    exists_small_real_line_eval_ne_zero P baseJet targetJet htarget (lt_min hρ hδ)
  have hερ : ε ≤ ρ := (hεmin.trans_le (min_le_left _ _)).le
  have hεδ : |ε| < δ := by
    rw [abs_of_pos hε]
    exact hεmin.trans_le (min_le_right _ _)
  have hpos : ∀ p, 0 < primeDyadicWeight u p + ε * a p :=
    positive_finsupp_perturbation_of_le
      (primeDyadicWeight u) (primeDyadicWeight_pos u) a hε.le hερ hρpos
  obtain ⟨C', hC'⟩ := primeLogPerturbedGauge_bounded u a ε C hu
  have hcoord : baseJet + ε • L a =
      fun i => baseJet i + (ε : ℂ) * (targetJet i - baseJet i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [ha]
    simp
  have hdetEscape : MvPolynomial.eval (baseJet + ε • L a) P ≠ 0 := by
    rw [hcoord]
    exact hescape
  refine ⟨a, ε, C', hε,
    (hεmin.trans_le (min_le_left _ _)).trans hρη, ?_,
    hδgauge ε hεδ, hC', ?_, primeLogPerturbedGauge_changeSet_finite u a ε, ?_⟩
  · simpa [primeLogPerturbedMass] using hpos
  · intro p
    rw [primeDyadicWeight_perturbedGauge u a ε (by
      simpa [primeLogPerturbedMass] using hpos) p]
    rfl
  · rw [eval_coefficientPatternDeterminant] at hdetEscape
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdetEscape

/-- **Prime-log coefficient-pattern fullness.** For every finite injective translate packet, every
finite set of distinct jet monomials, and every polynomial coefficient-degree bound, a single
finitely supported positive prime-mass perturbation makes the complete expanded evaluation matrix
full rank.  The evaluation bases are chosen so that all row-by-translate nodes are distinct and lie
in the upper half-plane. -/
theorem primeDyadic_polynomialCoefficientPattern_fullRank_escape
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (q : ℕ) (shift : ι → ℂ) (hshift : Function.Injective shift)
    (orders : ι → ℕ)
    (jetExponent : κ → ((Σ i, Fin (orders i)) →₀ ℕ))
    (hjet : Function.Injective jetExponent)
    (u : Nat.Primes → ℝ)
    (baseJet : Fin (Fintype.card (κ × Fin (q + 1))) ×
      (Σ i, Fin (orders i)) → ℂ)
    {η : ℝ} (hη : 0 < η) :
    let pattern := κ × Fin (q + 1)
    let n := Fintype.card pattern
    ∃ base : Fin n → ℂ, ∃ a : Nat.Primes →₀ ℝ, ∃ ε : ℝ,
      0 < ε ∧ ε < η ∧
      Function.Injective (fun x : Fin n × ι => base x.1 + shift x.2) ∧
      (∀ x : Fin n × ι, 0 < (base x.1 + shift x.2).im) ∧
      (∀ p, 0 < primeDyadicWeight u p + ε * a p) ∧
      IsUnit (Matrix.of fun r b =>
        (base r) ^ ((Fintype.equivFin pattern).symm b).2.val *
          (jetExponent ((Fintype.equivFin pattern).symm b).1).prod
            (fun i e => (baseJet + ε •
              ((reshapeCombinedJets (Fin n) ι orders).comp
                (cauchyJetRealLinearCombination
                  (fun x : Fin n × ι => base x.1 + shift x.2)
                  (fun x => orders x.2) primeLogSupport)) a) (r, i) ^ e) :
        Matrix (Fin n) (Fin n) ℂ) := by
  dsimp only
  let pattern := κ × Fin (q + 1)
  let n := Fintype.card pattern
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound shift
  obtain ⟨base, targetJet, hbase, hnodes, hfullTarget⟩ :=
    exists_noncolliding_fullRank_polynomialCoefficientMonomial_packet
      q jetExponent hjet shift hshift H
  have hupper : ∀ x : Fin n × ι, 0 < (base x.1 + shift x.2).im := by
    intro x
    rw [Complex.add_im]
    linarith [hbase x.1, hH x.2]
  let degree : Fin n → ℕ := fun b =>
    ((Fintype.equivFin pattern).symm b).2.val
  let exponent : Fin n → ((Σ i, Fin (orders i)) →₀ ℕ) := fun b =>
    jetExponent ((Fintype.equivFin pattern).symm b).1
  obtain ⟨a, ε, hε, hεη, hpos, hfull⟩ :=
    positive_coefficientPattern_fullRank_escape
      (fun x : Fin n × ι => base x.1 + shift x.2) hnodes hupper orders
      base degree exponent (fun x => targetJet x.1 x.2) hfullTarget
      (primeDyadicWeight u) (primeDyadicWeight_pos u) baseJet hη
  exact ⟨base, a, ε, hε, hεη, hnodes, hupper, hpos, hfull⟩

/-- **Bounded-gauge coefficient-pattern fullness.** The complete rank-defect locus for every finite
jet-monomial support and coefficient-degree bound has empty interior at every bounded prime-log
gauge: a finitely supported perturbation inside every uniform gauge ball produces one noncolliding
upper-half-plane packet whose expanded evaluation matrix has full rank. -/
theorem primeDyadic_polynomialCoefficientPattern_fullRank_escape_in_gaugeBall
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (q : ℕ) (shift : ι → ℂ) (hshift : Function.Injective shift)
    (orders : ι → ℕ)
    (jetExponent : κ → ((Σ i, Fin (orders i)) →₀ ℕ))
    (hjet : Function.Injective jetExponent)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (baseJet : Fin (Fintype.card (κ × Fin (q + 1))) ×
      (Σ i, Fin (orders i)) → ℂ)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    let pattern := κ × Fin (q + 1)
    let n := Fintype.card pattern
    ∃ base : Fin n → ℂ, ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      Function.Injective (fun x : Fin n × ι => base x.1 + shift x.2) ∧
      (∀ x : Fin n × ι, 0 < (base x.1 + shift x.2).im) ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      (∀ p, primeDyadicWeight (primeLogPerturbedGauge u a ε) p =
        primeDyadicWeight u p + ε * a p) ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      IsUnit (Matrix.of fun r b =>
        (base r) ^ ((Fintype.equivFin pattern).symm b).2.val *
          (jetExponent ((Fintype.equivFin pattern).symm b).1).prod
            (fun i e => (baseJet + ε •
              ((reshapeCombinedJets (Fin n) ι orders).comp
                (cauchyJetRealLinearCombination
                  (fun x : Fin n × ι => base x.1 + shift x.2)
                  (fun x => orders x.2) primeLogSupport)) a) (r, i) ^ e) :
        Matrix (Fin n) (Fin n) ℂ) := by
  dsimp only
  let pattern := κ × Fin (q + 1)
  let n := Fintype.card pattern
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound shift
  obtain ⟨base, targetJet, hbase, hnodes, hfullTarget⟩ :=
    exists_noncolliding_fullRank_polynomialCoefficientMonomial_packet
      q jetExponent hjet shift hshift H
  have hupper : ∀ x : Fin n × ι, 0 < (base x.1 + shift x.2).im := by
    intro x
    rw [Complex.add_im]
    linarith [hbase x.1, hH x.2]
  let degree : Fin n → ℕ := fun b =>
    ((Fintype.equivFin pattern).symm b).2.val
  let exponent : Fin n → ((Σ i, Fin (orders i)) →₀ ℕ) := fun b =>
    jetExponent ((Fintype.equivFin pattern).symm b).1
  obtain ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hmass, hfinite, hfull⟩ :=
    coefficientPattern_fullRank_escape_in_gaugeBall
      (fun x : Fin n × ι => base x.1 + shift x.2) hnodes hupper orders
      base degree exponent (fun x => targetJet x.1 x.2) hfullTarget
      u C hu baseJet hηTime hηGauge
  exact ⟨base, a, ε, C', hε, hεη, hnodes, hupper, hpos, hgauge,
    hbounded, hmass, hfinite, hfull⟩

/-- **Actual normalized coefficient-pattern fullness.** The bounded-gauge escape theorem is realized
by the normalized Cauchy jets of the actual perturbed prime-log Herglotz source, not an auxiliary
jet packet. -/
theorem primeDyadic_actualNormalizedCoefficientPattern_fullRank_escape_in_gaugeBall
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (q : ℕ) (shift : ι → ℂ) (hshift : Function.Injective shift)
    (orders : ι → ℕ)
    (jetExponent : κ → ((Σ i, Fin (orders i)) →₀ ℕ))
    (hjet : Function.Injective jetExponent)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    let pattern := κ × Fin (q + 1)
    let n := Fintype.card pattern
    ∃ base : Fin n → ℂ, ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      Function.Injective (fun x : Fin n × ι => base x.1 + shift x.2) ∧
      (∀ x : Fin n × ι, 0 < (base x.1 + shift x.2).im) ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      IsUnit (Matrix.of fun r b =>
        (base r) ^ ((Fintype.equivFin pattern).symm b).2.val *
          (jetExponent ((Fintype.equivFin pattern).symm b).1).prod
            (fun i e =>
              (primeLogCauchyJetPacket (primeLogPerturbedGauge u a ε)
                (fun x : Fin n × ι => base x.1 + shift x.2)
                (fun x => orders x.2)
                (rowJetIndexEquiv (Fin n) ι orders (r, i))) ^ e) :
        Matrix (Fin n) (Fin n) ℂ) := by
  dsimp only
  let pattern := κ × Fin (q + 1)
  let n := Fintype.card pattern
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound shift
  obtain ⟨base, targetJet, hbase, hnodes, hfullTarget⟩ :=
    exists_noncolliding_fullRank_polynomialCoefficientMonomial_packet
      q jetExponent hjet shift hshift H
  let nodes : Fin n × ι → ℂ := fun x => base x.1 + shift x.2
  let combinedOrders : Fin n × ι → ℕ := fun x => orders x.2
  have hupper : ∀ x : Fin n × ι, 0 < (nodes x).im := by
    intro x
    change 0 < (base x.1 + shift x.2).im
    rw [Complex.add_im]
    linarith [hbase x.1, hH x.2]
  let degree : Fin n → ℕ := fun b =>
    ((Fintype.equivFin pattern).symm b).2.val
  let exponent : Fin n → ((Σ i, Fin (orders i)) →₀ ℕ) := fun b =>
    jetExponent ((Fintype.equivFin pattern).symm b).1
  let baseJet : Fin n × (Σ i, Fin (orders i)) → ℂ :=
    (reshapeCombinedJets (Fin n) ι orders)
      (primeLogCauchyJetPacket u nodes combinedOrders)
  obtain ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hmass, hfinite, hfull⟩ :=
    coefficientPattern_fullRank_escape_in_gaugeBall
      nodes hnodes hupper orders base degree exponent
      (fun x => targetJet x.1 x.2) hfullTarget u C hu baseJet hηTime hηGauge
  have hpacket := primeLogCauchyJetPacket_perturbedGauge u C
    (fun p => (le_abs_self (u p)).trans (hu p)) nodes hupper combinedOrders a ε hpos
  let L := (reshapeCombinedJets (Fin n) ι orders).comp
    (cauchyJetRealLinearCombination nodes combinedOrders primeLogSupport)
  have hcoord : baseJet + ε • L a =
      (reshapeCombinedJets (Fin n) ι orders)
        (primeLogCauchyJetPacket (primeLogPerturbedGauge u a ε) nodes combinedOrders) := by
    rw [hpacket]
    rfl
  rw [hcoord] at hfull
  refine ⟨base, a, ε, C', hε, hεη, hnodes, ?_, hpos, hgauge, hbounded,
    hfinite, ?_⟩
  · simpa [nodes] using hupper
  · simpa [degree, exponent, nodes, combinedOrders, reshapeCombinedJets] using hfull

/-- The nonzero column factor contributed by converting one normalized jet monomial to actual
derivatives. -/
noncomputable def jetMonomialFactorialScale
    {ι : Type*} {orders : ι → ℕ}
    (β : (Σ i, Fin (orders i)) →₀ ℕ) : ℂ :=
  β.prod fun s e => (s.2.1.factorial : ℂ) ^ e

theorem jetMonomialFactorialScale_ne_zero
    {ι : Type*} {orders : ι → ℕ}
    (β : (Σ i, Fin (orders i)) →₀ ℕ) :
    jetMonomialFactorialScale β ≠ 0 := by
  rw [jetMonomialFactorialScale, Finsupp.prod_ne_zero_iff]
  intro s hs
  exact pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero s.2.1)

theorem jetMonomial_actual_eq_factorialScale_mul_normalized
    {ι : Type*} {orders : ι → ℕ}
    (β : (Σ i, Fin (orders i)) →₀ ℕ)
    (normalized actual : (Σ i, Fin (orders i)) → ℂ)
    (hactual : ∀ s, actual s = (s.2.1.factorial : ℂ) * normalized s) :
    β.prod (fun s e => actual s ^ e) =
      jetMonomialFactorialScale β * β.prod (fun s e => normalized s ^ e) := by
  rw [jetMonomialFactorialScale, ← Finsupp.prod_mul]
  apply Finsupp.prod_congr
  intro s hs
  rw [hactual, mul_pow]

/-- Multiplying every normalized jet coordinate by its nonzero factorial preserves full
coefficient-pattern rank. -/
theorem coefficientPattern_isUnit_actual_of_normalized
    {row ι : Type*} [Fintype row] [DecidableEq row]
    {orders : ι → ℕ}
    (base : row → ℂ) (degree : row → ℕ)
    (jetExponent : row → ((Σ i, Fin (orders i)) →₀ ℕ))
    (normalized actual : row → (Σ i, Fin (orders i)) → ℂ)
    (hactual : ∀ r s, actual r s = (s.2.1.factorial : ℂ) * normalized r s)
    (hnorm : IsUnit (Matrix.of fun r b =>
      base r ^ degree b * (jetExponent b).prod (fun s e => normalized r s ^ e) :
      Matrix row row ℂ)) :
    IsUnit (Matrix.of fun r b =>
      base r ^ degree b * (jetExponent b).prod (fun s e => actual r s ^ e) :
      Matrix row row ℂ) := by
  let A : Matrix row row ℂ := Matrix.of fun r b =>
    base r ^ degree b * (jetExponent b).prod (fun s e => normalized r s ^ e)
  let scale : row → ℂ := fun b => jetMonomialFactorialScale (jetExponent b)
  have hscale : ∀ b, scale b ≠ 0 := fun b => jetMonomialFactorialScale_ne_zero _
  have hdiag : IsUnit (Matrix.diagonal scale) := by
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro b
    exact isUnit_iff_ne_zero.mpr (hscale b)
  have hmul : IsUnit (A * Matrix.diagonal scale) := hnorm.mul hdiag
  have heq : A * Matrix.diagonal scale = Matrix.of fun r b =>
      base r ^ degree b * (jetExponent b).prod (fun s e => actual r s ^ e) := by
    ext r b
    rw [Matrix.mul_diagonal]
    change (base r ^ degree b *
      (jetExponent b).prod (fun s e => normalized r s ^ e)) * scale b =
        base r ^ degree b *
          (jetExponent b).prod (fun s e => actual r s ^ e)
    rw [jetMonomial_actual_eq_factorialScale_mul_normalized
      (jetExponent b) (normalized r) (actual r) (hactual r)]
    simp only [scale]
    ring
  rw [heq] at hmul
  exact hmul

/-- **Actual differential coefficient-pattern fullness.** Every finite polynomial-coefficient
pattern in actual iterated derivatives of finitely many prime-log translates has full evaluation
rank after a finitely supported perturbation in every bounded-gauge neighborhood. -/
theorem primeDyadic_actualDifferentialCoefficientPattern_fullRank_escape_in_gaugeBall
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (q : ℕ) (shift : ι → ℂ) (hshift : Function.Injective shift)
    (orders : ι → ℕ)
    (jetExponent : κ → ((Σ i, Fin (orders i)) →₀ ℕ))
    (hjet : Function.Injective jetExponent)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    let pattern := κ × Fin (q + 1)
    let n := Fintype.card pattern
    ∃ base : Fin n → ℂ, ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      Function.Injective (fun x : Fin n × ι => base x.1 + shift x.2) ∧
      (∀ x : Fin n × ι, 0 < (base x.1 + shift x.2).im) ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      IsUnit (Matrix.of fun r b =>
        (base r) ^ ((Fintype.equivFin pattern).symm b).2.val *
          (jetExponent ((Fintype.equivFin pattern).symm b).1).prod
            (fun i e =>
              (primeLogDifferentialJetPacket (primeLogPerturbedGauge u a ε)
                (fun x : Fin n × ι => base x.1 + shift x.2)
                (fun x => orders x.2)
                (rowJetIndexEquiv (Fin n) ι orders (r, i))) ^ e) :
        Matrix (Fin n) (Fin n) ℂ) := by
  dsimp only
  let pattern := κ × Fin (q + 1)
  let n := Fintype.card pattern
  obtain ⟨base, a, ε, C', hε, hεη, hnodes, hupper, hpos, hgauge, hbounded,
      hfinite, hnorm⟩ :=
    primeDyadic_actualNormalizedCoefficientPattern_fullRank_escape_in_gaugeBall
      q shift hshift orders jetExponent hjet u C hu hηTime hηGauge
  let nodes : Fin n × ι → ℂ := fun x => base x.1 + shift x.2
  let combinedOrders : Fin n × ι → ℕ := fun x => orders x.2
  let u' := primeLogPerturbedGauge u a ε
  let degree : Fin n → ℕ := fun b =>
    ((Fintype.equivFin pattern).symm b).2.val
  let exponent : Fin n → ((Σ i, Fin (orders i)) →₀ ℕ) := fun b =>
    jetExponent ((Fintype.equivFin pattern).symm b).1
  let normalized : Fin n → (Σ i, Fin (orders i)) → ℂ := fun r s =>
    primeLogCauchyJetPacket u' nodes combinedOrders
      (rowJetIndexEquiv (Fin n) ι orders (r, s))
  let actual : Fin n → (Σ i, Fin (orders i)) → ℂ := fun r s =>
    primeLogDifferentialJetPacket u' nodes combinedOrders
      (rowJetIndexEquiv (Fin n) ι orders (r, s))
  have hu' : ∀ p, u' p ≤ C' := fun p =>
    (le_abs_self _).trans (hbounded p)
  have hactual : ∀ r s,
      actual r s = (s.2.1.factorial : ℂ) * normalized r s := by
    intro r s
    have h := iteratedDeriv_primeLogHerglotz_eq_factorial_mul_packet
      u' C' hu' nodes (by simpa [nodes] using hupper) combinedOrders
      (rowJetIndexEquiv (Fin n) ι orders (r, s))
    simpa [actual, normalized, primeLogDifferentialJetPacket,
      rowJetIndexEquiv, combinedOrders] using h
  have hnorm' : IsUnit (Matrix.of fun r b =>
      base r ^ degree b * (exponent b).prod (fun s e => normalized r s ^ e) :
      Matrix (Fin n) (Fin n) ℂ) := by
    simpa [degree, exponent, normalized, nodes, combinedOrders, u'] using hnorm
  have hactualFull := coefficientPattern_isUnit_actual_of_normalized
    base degree exponent normalized actual hactual hnorm'
  refine ⟨base, a, ε, C', hε, hεη, hnodes, hupper, hpos, hgauge, hbounded,
    hfinite, ?_⟩
  simpa [degree, exponent, actual, nodes, combinedOrders, u'] using hactualFull

/-- The finite-jet rank-defect locus for one coefficient pattern. -/
def coefficientPatternRankDefect
    {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → ℂ) (degree : row → ℕ) (jetExponent : row → (σ →₀ ℕ)) :
    Set (row × σ → ℂ) :=
  {y | ¬ IsUnit (Matrix.of fun a b =>
    base a ^ degree b * (jetExponent b).prod (fun i e => y (a, i) ^ e) :
    Matrix row row ℂ)}

theorem coefficientPatternRankDefect_eq_zeroSet
    {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → ℂ) (degree : row → ℕ) (jetExponent : row → (σ →₀ ℕ)) :
    coefficientPatternRankDefect base degree jetExponent =
      {y | MvPolynomial.eval y
        (coefficientPatternDeterminant base degree jetExponent) = 0} := by
  ext y
  change (¬ IsUnit (Matrix.of fun a b =>
    base a ^ degree b * (jetExponent b).prod (fun i e => y (a, i) ^ e) :
    Matrix row row ℂ)) ↔
      MvPolynomial.eval y
        (coefficientPatternDeterminant base degree jetExponent) = 0
  rw [eval_coefficientPatternDeterminant]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simp

theorem coefficientPatternRankDefect_isClosed
    {row σ : Type*} [Fintype row] [DecidableEq row]
    (base : row → ℂ) (degree : row → ℕ) (jetExponent : row → (σ →₀ ℕ)) :
    IsClosed (coefficientPatternRankDefect base degree jetExponent) := by
  rw [coefficientPatternRankDefect_eq_zeroSet]
  exact mvPolynomial_zero_set_isClosed _

/-- A coefficient-pattern rank defect is nowhere dense as soon as one full-rank target packet
exists. -/
theorem coefficientPatternRankDefect_isNowhereDense_of_isUnit
    {row σ : Type*} [Fintype row] [DecidableEq row] [Fintype σ]
    (base : row → ℂ) (degree : row → ℕ) (jetExponent : row → (σ →₀ ℕ))
    (target : row × σ → ℂ)
    (hfull : IsUnit (Matrix.of fun a b =>
      base a ^ degree b * (jetExponent b).prod (fun i e => target (a, i) ^ e) :
      Matrix row row ℂ)) :
    IsNowhereDense (coefficientPatternRankDefect base degree jetExponent) := by
  rw [coefficientPatternRankDefect_eq_zeroSet]
  exact mvPolynomial_zero_set_isNowhereDense _
    (coefficientPatternDeterminant_ne_zero_of_isUnit
      base degree jetExponent target hfull)

end GaloisForLFunctions.HTGeometry
