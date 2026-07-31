import GaloisForLFunctions.HTGeometry.PolynomialPowerActiveAtomGap

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

def degreeDPolynomialPatterns (M D : ℕ) :
    Finset (Fin M → Fin (D + 1)) :=
  Finset.univ.filter fun p => (∑ r, (p r : ℕ)) = D

def polynomialPatternSurvivors (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (M : ℕ) :
    Finset (Fin M → Fin (D + 1)) :=
  (degreeDPolynomialPatterns M D).filter fun p =>
    polynomialPatternWeightPoly n D K τ Q p ≠ 0

theorem polynomialPatternSurvivors_count
    {n D K τ M : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (hp : p ∈ polynomialPatternSurvivors n D K τ Q M) :
    (∑ r, (p r : ℕ)) = D :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2

theorem polynomialPatternSurvivors_weightPoly_ne_zero
    {n D K τ M : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (hp : p ∈ polynomialPatternSurvivors n D K τ Q M) :
    polynomialPatternWeightPoly n D K τ Q p ≠ 0 :=
  (Finset.mem_filter.mp hp).2

theorem mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero
    {n D K τ M q : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (hcount : (∑ r, (p r : ℕ)) = D) (hlarge : K + n ≤ q)
    (hw : aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) ≠ 0) :
    p ∈ polynomialPatternSurvivors n D K τ Q M := by
  rw [polynomialPatternSurvivors, Finset.mem_filter]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcount⟩, ?_⟩
  intro hzero
  apply hw
  rw [aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D K τ Q p hcount hlarge,
    hzero, Polynomial.eval_zero]

theorem polynomialPatternSurvivors_nonempty_of_aevalWeight_ne_zero
    {n D K τ M q : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (hcount : (∑ r, (p r : ℕ)) = D) (hlarge : K + n ≤ q)
    (hw : aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) ≠ 0) :
    (polynomialPatternSurvivors n D K τ Q M).Nonempty :=
  ⟨p, mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hcount hlarge hw⟩

theorem exists_nonzero_intPolynomial_of_mem_polynomialPatternSurvivors
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    {p : Fin M → Fin (D + 1)}
    (hp : p ∈ polynomialPatternSurvivors n D K τ Q M) :
    ∃ W : Polynomial ℤ, W ≠ 0 ∧ ∀ q, K + n ≤ q →
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
        ((W.eval (q : ℤ) : ℤ) : ℂ) := by
  classical
  choose c hc using hQint
  let W := polynomialPatternWeightPolyInt n D K τ Q c p
  have hmap := map_polynomialPatternWeightPolyInt n D K τ Q c hc p
  have hW : W ≠ 0 := by
    intro hzero
    apply polynomialPatternSurvivors_weightPoly_ne_zero hp
    have hzero' : polynomialPatternWeightPolyInt n D K τ Q c p = 0 := by
      simpa [W] using hzero
    rw [← hmap, hzero', Polynomial.map_zero]
  refine ⟨W, hW, fun q hlarge => ?_⟩
  rw [aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D K τ Q p
    (polynomialPatternSurvivors_count hp) hlarge]
  rw [← hmap]
  simp [W]

theorem polynomialPatternSurvivors_eventually_weight_ne_zero
    {n D K τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    ∀ᶠ q : ℕ in atTop, ∀ p ∈ polynomialPatternSurvivors n D K τ Q M,
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) ≠ 0 := by
  classical
  rw [Filter.eventually_all]
  intro p
  by_cases hp : p ∈ polynomialPatternSurvivors n D K τ Q M
  · have hpoly := polynomialPatternSurvivors_weightPoly_ne_zero hp
    obtain ⟨Q₀, hQ₀⟩ := poly_eventually_ne_zero_nat
      (polynomialPatternWeightPoly n D K τ Q p) hpoly
    filter_upwards [eventually_ge_atTop (max Q₀ (K + n))] with q hq hp'
    rw [aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D K τ Q p
      (polynomialPatternSurvivors_count hp) (by omega)]
    exact hQ₀ q (by omega)
  · exact Eventually.of_forall fun q hp' => (hp hp').elim

/-- Every count-`D` atom supported in a translated interval is the shifted key
of a bounded pattern in that interval. -/
theorem exists_boundedPattern_of_atom_support_interval
    {D q K M : ℕ} (ν : ℕ →₀ ℕ)
    (hcount : ν.sum (fun _ k => k) = D)
    (hsupp : ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i < q - K + M) :
    ∃ p : Fin M → Fin (D + 1),
      (∑ r, (p r : ℕ)) = D ∧ shiftedAtomPatternKey q K p = ν := by
  classical
  let t : Fin D → ℕ := tupleOfFinsupp ν D hcount
  have htSupp : ∀ j, q - K ≤ t j ∧ t j < q - K + M := by
    intro j
    have hkeyj : key t (t j) ≠ 0 := by
      rw [key_count_map]
      apply Multiset.count_ne_zero.mpr
      simp
    have hνj : ν (t j) ≠ 0 := by
      rw [← key_tupleOfFinsupp ν D hcount]
      exact hkeyj
    exact hsupp (t j) hνj
  let g : Fin D → Fin M := fun j => ⟨t j - (q - K), by
    have hj := htSupp j
    omega⟩
  have htEq : ∀ j, t j = windowShift q K (g j : ℕ) := by
    intro j
    have hj := (htSupp j).1
    dsimp [g, windowShift]
    omega
  have hgCount : (key (fun j => (g j : ℕ))).sum (fun _ k => k) = D :=
    key_total_count (fun j => (g j : ℕ))
  have hgSupp : ∀ r, key (fun j => (g j : ℕ)) r ≠ 0 → r < M := by
    intro r hr
    rw [key_count_map] at hr
    have hrmem : r ∈ Multiset.map (fun j => (g j : ℕ))
        (Finset.univ : Finset (Fin D)).val := Multiset.count_ne_zero.mp hr
    rw [Multiset.mem_map] at hrmem
    obtain ⟨j, hj, hjr⟩ := hrmem
    rw [← hjr]
    exact (g j).isLt
  let p : Fin M → Fin (D + 1) :=
    boundedPatternOfFinsupp (key (fun j => (g j : ℕ))) D M hgCount
  have hpCount : (∑ r, (p r : ℕ)) = D :=
    boundedPatternOfFinsupp_count _ D M hgCount hgSupp
  have hg : g ∈ atomPatternAssignments p := by
    rw [mem_atomPatternAssignments]
    exact (atomPatternKey_boundedPatternOfFinsupp _ D M hgCount hgSupp).symm
  refine ⟨p, hpCount, ?_⟩
  calc
    shiftedAtomPatternKey q K p =
        key (fun j => windowShift q K (g j : ℕ)) :=
      (key_windowShift_eq_shiftedAtomPatternKey p g hg).symm
    _ = key t := congrArg key (funext htEq).symm
    _ = ν := key_tupleOfFinsupp ν D hcount

end

end GaloisForLFunctions
