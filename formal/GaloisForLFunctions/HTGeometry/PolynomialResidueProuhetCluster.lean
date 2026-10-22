import GaloisForLFunctions.HTGeometry.PolynomialPhaseLockAssembly

/-!
# A residue class of coefficients carrying a Prouhet-locked pattern cluster

For a polynomial `Q` in `n + 2` variables with integer coefficients and positive maximal jet degree
`D` (largest number of dependent-variable factors in a monomial), fix a residue `τ < D`. Along the
coefficient indices `N = D q + τ`, the atom weights of `Q(X, F, …, F⁽ⁿ⁾)` at window-shifted
multiplicity patterns are values `W_p(q)` of nonzero integer polynomials, for all `q ≥ K + n`. The
module produces a nonempty finite set `S` of such surviving patterns together with a nonempty
sub-cluster `C ⊆ S` whose members share all moments below `⌈β⌉` and whose pairwise difference
polynomials are divisible by `(X - 1)^{⌈β⌉}`.

## Main results

- `exists_residueProuhetCluster`: for `2 < β`, integer-coefficient `Q` with `D > 0` and `τ < D`,
  there exist `K, M`, patterns `S ⊇ C` (both nonempty) and nonzero integer polynomials `W p` with
  `aevalWeight n (D q + τ) Q (shiftedAtomPatternKey q K p) = W_p(q)` for `p ∈ S`, `q ≥ K + n`, and
  for `p, r ∈ C`: `m_j(p) = m_j(r)` for `j < ⌈β⌉` and `(X - 1)^{⌈β⌉}` divides
  `atomPatternDifferencePolynomial p r`.

## Hypotheses

Unconditional. The theorem assumes `2 < β`, integrality of every coefficient of `Q`,
`0 < magnitudeMaxJetDegree n Q`, and `τ < magnitudeMaxJetDegree n Q`. No differential relation for
a power series is assumed.
-/

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

set_option maxHeartbeats 600000 in
/-- Assuming `2 < β`, integer coefficients, `D = magnitudeMaxJetDegree n Q > 0` and `τ < D`: a
nonempty set `S` of surviving patterns with integer-polynomial weights `W_p(q)` on the residue class
`N = D q + τ`, and a nonempty cluster `C ⊆ S` with equal moments below `⌈β⌉` and `(X - 1)^{⌈β⌉}`
dividing every pairwise difference polynomial. -/
theorem exists_residueProuhetCluster
    {β : ℝ} (hβ : 2 < β) {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hDpos : 0 < magnitudeMaxJetDegree n Q)
    (τ : ℕ) (hτ : τ < magnitudeMaxJetDegree n Q) :
    ∃ (K M : ℕ)
        (S C : Finset (Fin M → Fin (magnitudeMaxJetDegree n Q + 1)))
        (W : (Fin M → Fin (magnitudeMaxJetDegree n Q + 1)) → Polynomial ℤ),
      S.Nonempty ∧ C.Nonempty ∧ C ⊆ S ∧
      (∀ p ∈ S, W p ≠ 0 ∧ ∀ q, K + n ≤ q →
        aevalWeight n (magnitudeMaxJetDegree n Q * q + τ) Q
            (shiftedAtomPatternKey q K p) =
          (((W p).eval (q : ℤ) : ℤ) : ℂ)) ∧
      (∀ p ∈ C, ∀ r ∈ C,
        (∀ j < Nat.ceil β,
          polynomialPatternMoment p j = polynomialPatternMoment r j) ∧
        (Polynomial.X - 1) ^ Nat.ceil β ∣
          atomPatternDifferencePolynomial p r) := by
  classical
  obtain ⟨anchor, ha, haD, haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  rw [← haD] at hDpos hτ haMax ⊢
  let D := jetMonomialDegree n anchor
  let J := jetMonomialOrder n anchor
  have hD : 0 < D := by simpa [D, haD] using hDpos
  have hτD : τ < D := by simpa [D, haD] using hτ
  obtain ⟨Kshift, δ, Qres, hres⟩ :=
    exists_eventually_balancedKey_nonzero_exact_residue ha hD τ hτD
  obtain ⟨Kconf, cgap, hcgap, hgapEv⟩ :=
    exists_eventually_activeAtom_powerGap_or_window hβ Q ha haD haMax hD δ
  obtain ⟨Qgap, hgap⟩ := Filter.eventually_atTop.mp hgapEv
  let K := Kshift + Kconf
  let M := 2 * Kconf + 1
  let q₀ := max Qres (max (Qgap + Kshift) (max (K + n) (Kshift + J + 1)))
  have hqres : Qres ≤ q₀ := le_max_left _ _
  have hqgap : Qgap ≤ q₀ - Kshift := by dsimp [q₀]; omega
  have hqlarge : K + n ≤ q₀ := by dsimp [q₀]; omega
  have hqshift : Kshift ≤ q₀ := by dsimp [q₀]; omega
  have hqrawPos : 0 < q₀ - Kshift := by dsimp [q₀]; omega
  let qraw := q₀ - Kshift
  let s : Fin D → ℕ := fun i => qraw + δ i
  have hres₀ := hres q₀ hqres
  have hmem : key s ∈ (sigmaIdx n (D * q₀ + τ) Q).image (atomKeyOf n) := by
    simpa only [D, qraw, s] using hres₀.1
  have hweight : aevalWeight n (D * q₀ + τ) Q (key s) ≠ 0 := by
    simpa only [D, qraw, s] using hres₀.2.1
  have hinv : (key s).sum (fun i k => i * k) + magnitudeShiftCode n Q anchor =
      D * q₀ + τ + magnitudeMaxJetOrder n Q := by
    simpa only [D, qraw, s] using hres₀.2.2
  have hJle : J ≤ ∑ i, s i := by
    obtain ⟨i₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
    have hbase : J ≤ qraw := by dsimp [qraw, q₀]; omega
    exact hbase.trans ((show qraw ≤ s i₀ by simp [s]).trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)))
  let Nraw := (∑ i, s i) + anchor 0 - J
  have hwraw := witness_sum_add_shiftCode Q ha δ Nraw rfl hJle
  have hNraw : Nraw = D * q₀ + τ := by
    rw [key_weighted_sum] at hinv
    change (∑ i, s i) + magnitudeShiftCode n Q anchor =
      Nraw + magnitudeMaxJetOrder n Q at hwraw
    omega
  have hgap₀ := hgap qraw hqgap (key s) (by
    simpa [hNraw, Nraw, J, D, s, qraw] using hmem)
  have hwitnessWindow :
      (key s).sum (fun _ k => k) = D ∧
        ∀ i, key s i ≠ 0 → qraw - Kconf ≤ i ∧ i ≤ qraw + Kconf := by
    rcases hgap₀ with hwin | hlose
    · simpa only [D, s] using hwin
    · have hpowPos : 0 < (qraw : ℝ) ^ (β - 2) :=
        Real.rpow_pos_of_pos (by exact_mod_cast hqrawPos) _
      have hcpos : 0 < cgap * (qraw : ℝ) ^ (β - 2) := mul_pos hcgap hpowPos
      have hself : (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) +
          cgap * (qraw : ℝ) ^ (β - 2) ≤
          (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) := by
        simpa only [s] using hlose
      linarith
  have hδle : ∀ i, δ i ≤ Kconf := by
    intro i
    have hkeyi : key s (s i) ≠ 0 := by
      rw [key_count_map]
      apply Multiset.count_ne_zero.mpr
      simp
    have hi := (hwitnessWindow.2 (s i) hkeyi).2
    dsimp [s] at hi
    omega
  let g : Fin D → Fin M := fun i => ⟨Kconf + δ i, by
    dsimp [M]
    have := hδle i
    omega⟩
  have hgCount : (key (fun i => (g i : ℕ))).sum (fun _ k => k) = D :=
    key_total_count (fun i => (g i : ℕ))
  have hgSupp : ∀ r, key (fun i => (g i : ℕ)) r ≠ 0 → r < M := by
    intro r hr
    rw [key_count_map] at hr
    have hrmem : r ∈ Multiset.map (fun i => (g i : ℕ))
        (Finset.univ : Finset (Fin D)).val := Multiset.count_ne_zero.mp hr
    rw [Multiset.mem_map] at hrmem
    obtain ⟨i, hi, hir⟩ := hrmem
    rw [← hir]
    exact (g i).isLt
  let pW : Fin M → Fin (D + 1) :=
    boundedPatternOfFinsupp (key (fun i => (g i : ℕ))) D M hgCount
  have hpWcount : (∑ r, (pW r : ℕ)) = D :=
    boundedPatternOfFinsupp_count _ D M hgCount hgSupp
  have hg : g ∈ atomPatternAssignments pW := by
    rw [mem_atomPatternAssignments]
    exact (atomPatternKey_boundedPatternOfFinsupp _ D M hgCount hgSupp).symm
  have hkeyW : shiftedAtomPatternKey q₀ K pW = key s := by
    calc
      shiftedAtomPatternKey q₀ K pW =
          key (fun i => windowShift q₀ K (g i : ℕ)) :=
        (key_windowShift_eq_shiftedAtomPatternKey pW g hg).symm
      _ = key s := by
        congr 1
        funext i
        dsimp [windowShift, K, g, s, qraw]
        omega
  let S := polynomialPatternSurvivors n D K τ Q M
  have hpWS : pW ∈ S := by
    apply mem_polynomialPatternSurvivors_of_aevalWeight_ne_zero hpWcount hqlarge
    simpa [hkeyW] using hweight
  have hS : S.Nonempty := ⟨pW, hpWS⟩
  have hpWFloor : polynomialPatternSourceSum pW + magnitudeShiftCode n Q anchor =
      D * K + τ + magnitudeMaxJetOrder n Q := by
    apply polynomialPattern_source_floor_eq_of_anchor_invariant pW hpWcount
      ((Nat.le_add_right K n).trans hqlarge)
    simpa [hkeyW] using hinv
  let T := polynomialPatternLeastSourceClass S hS
  have hT : T.Nonempty := polynomialPatternLeastSourceClass_nonempty S hS
  have hpWT : pW ∈ T := by
    dsimp [T]
    rw [polynomialPatternLeastSourceClass, Finset.mem_filter]
    refine ⟨hpWS, ?_⟩
    apply le_antisymm
    · have hfloor : ∀ p ∈ S, polynomialPatternSourceSum pW ≤
          polynomialPatternSourceSum p := by
        intro p hp
        have hpFloor := polynomialPattern_source_floor_of_survivor
          (Q := Q) (anchor := anchor) (by
            intro m hm hmD
            apply haMax m hm
            simpa [D, haD] using hmD) hp
        omega
      have hminmem : minimalPolynomialPatternSourceSum S hS ∈
          S.image polynomialPatternSourceSum := Finset.min'_mem _ _
      obtain ⟨p, hpS, hpEq⟩ := Finset.mem_image.mp hminmem
      rw [← hpEq]
      exact hfloor p hpS
    · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨pW, hpWS, rfl⟩)
  let C := polynomialPatternMinimalCluster (R := Nat.ceil β - 2) T hT
  have hC : C.Nonempty := polynomialPatternMinimalCluster_nonempty T hT
  choose cint hcint using hQint
  let W : (Fin M → Fin (D + 1)) → Polynomial ℤ := fun p =>
    polynomialPatternWeightPolyInt n D K τ Q cint p
  have hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D := fun p hp =>
    polynomialPatternSurvivors_count hp
  have hW : ∀ p ∈ S, W p ≠ 0 ∧ ∀ q, K + n ≤ q →
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
        (((W p).eval (q : ℤ) : ℤ) : ℂ) := by
    intro p hp
    have hmap := map_polynomialPatternWeightPolyInt n D K τ Q cint hcint p
    have hWne : W p ≠ 0 := by
      intro hzero
      apply polynomialPatternSurvivors_weightPoly_ne_zero hp
      rw [← hmap]
      have hz : polynomialPatternWeightPolyInt n D K τ Q cint p = 0 := by
        simpa [W] using hzero
      rw [hz, Polynomial.map_zero]
    refine ⟨hWne, fun q hq => ?_⟩
    rw [aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D K τ Q p
      (hcount p hp) hq, ← hmap]
    simp [W]
  refine ⟨K, M, S, C, W, hS, hC, ?_, hW, ?_⟩
  · exact (polynomialPatternMinimalCluster_subset T hT).trans
      (polynomialPatternLeastSourceClass_subset S hS)
  · intro p hp r hr
    exact ⟨polynomialPatternCluster_moments S hS hcount hp hr,
      polynomialPatternCluster_prouhet_dvd S hS hcount hp hr⟩

end

end GaloisForLFunctions
