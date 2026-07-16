import GaloisForLFunctions.HTGeometry.PolynomialADEPhaseIdentity

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

/-- A bounded pattern obtained by restricting a count-`D` multiplicity key
to offsets below `M`. -/
noncomputable def boundedPatternOfFinsupp (ν : ℕ →₀ ℕ) (D M : ℕ)
    (hcount : ν.sum (fun _ k => k) = D) : Fin M → Fin (D + 1) :=
  fun r => ⟨ν (r : ℕ), by
    have hr := finsupp_apply_le_count ν (r : ℕ)
    rw [hcount] at hr
    omega⟩

theorem atomPatternKey_boundedPatternOfFinsupp
    (ν : ℕ →₀ ℕ) (D M : ℕ)
    (hcount : ν.sum (fun _ k => k) = D)
    (hsupp : ∀ r, ν r ≠ 0 → r < M) :
    atomPatternKey (boundedPatternOfFinsupp ν D M hcount) = ν := by
  classical
  ext r
  rw [atomPatternKey_apply]
  split_ifs with hr
  · rfl
  · have hzero : ν r = 0 := by
      by_contra hne
      exact hr (hsupp r hne)
    simp [hzero]

theorem boundedPatternOfFinsupp_count
    (ν : ℕ →₀ ℕ) (D M : ℕ)
    (hcount : ν.sum (fun _ k => k) = D)
    (hsupp : ∀ r, ν r ≠ 0 → r < M) :
    ∑ j, (boundedPatternOfFinsupp ν D M hcount j : ℕ) = D := by
  rw [← atomPatternKey_count,
    atomPatternKey_boundedPatternOfFinsupp ν D M hcount hsupp, hcount]

/-- A prescribed residue class contains one fixed bounded pattern with
nonzero grouped weight at every sufficiently large exact level `D*q+τ`. -/
theorem exists_eventually_boundedPattern_nonzero_aevalWeight_residue
    {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor)
    (τ : ℕ) (hτ : τ < jetMonomialDegree n anchor) :
    ∃ (K M : ℕ)
        (p : Fin M → Fin (jetMonomialDegree n anchor + 1)) (Q₀ : ℕ),
      (∑ j, (p j : ℕ)) = jetMonomialDegree n anchor ∧
      ∀ q ≥ Q₀,
        shiftedAtomPatternKey q K p ∈
            (sigmaIdx n (jetMonomialDegree n anchor * q + τ) Q).image (atomKeyOf n) ∧
          aevalWeight n (jetMonomialDegree n anchor * q + τ) Q
            (shiftedAtomPatternKey q K p) ≠ 0 := by
  classical
  let D := jetMonomialDegree n anchor
  let J := jetMonomialOrder n anchor
  obtain ⟨δ, hδinj, Qbal, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight_residue ha hD τ
  let δ' : Fin D → ℕ := fun i => J + δ i
  have hδ'inj : Function.Injective δ' := by
    intro i j hij
    apply hδinj
    dsimp [δ'] at hij
    omega
  let C₀ := (∑ i, δ' i) + anchor 0 - J
  have hJsum : J ≤ (∑ i, δ' i) + anchor 0 := by
    obtain ⟨i₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
    have hi : J ≤ δ' i₀ := by simp [δ']
    exact hi.trans ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i₀)).trans (Nat.le_add_right _ _))
  have hNshape (q : ℕ) :
      (∑ i : Fin D, ((q + J) + δ i)) + anchor 0 - J = D * q + C₀ := by
    have hsum : (∑ i : Fin D, ((q + J) + δ i)) =
        D * q + ∑ i, δ' i := by
      simp only [δ', Finset.sum_add_distrib]
      simp [D]
      ring
    rw [hsum]
    dsimp [C₀]
    omega
  have hQbalJ : Qbal ≤ Qbal + J := Nat.le_add_right _ _
  have hdata₀ := hbalanced (Qbal + J) hQbalJ
  let N₀ := (∑ i : Fin D, ((Qbal + J) + δ i)) + anchor 0 - J
  have hN₀ : N₀ = D * Qbal + C₀ := by
    exact hNshape Qbal
  have hmodN₀ : Nat.ModEq D N₀ τ := by
    simpa only [D, J, N₀] using hdata₀.1
  have hmodC₀ : Nat.ModEq D C₀ τ := by
    exact (Nat.ModEq.modulus_mul_add (m := D) (a := Qbal) (b := C₀)).symm.trans
      (by simpa [hN₀] using hmodN₀)
  have hrem : C₀ % D = τ := by
    change C₀ % D = τ % D at hmodC₀
    have hτD : τ < D := by simpa [D] using hτ
    rw [Nat.mod_eq_of_lt hτD] at hmodC₀
    exact hmodC₀
  let K := C₀ / D
  have hC₀shape : D * K + τ = C₀ := by
    have hdiv := Nat.mod_add_div C₀ D
    rw [hrem] at hdiv
    dsimp [K]
    omega
  let Boff := magnitudeOffsetMax δ'
  let M := Boff + 1
  have hδ'M : ∀ i, δ' i < M := by
    intro i
    exact (offset_le_magnitudeOffsetMax δ' i).trans_lt (by dsimp [M]; omega)
  have hkeyCount : (key δ').sum (fun _ k => k) = D := key_total_count δ'
  have hkeySupp : ∀ r, key δ' r ≠ 0 → r < M := by
    intro r hr
    rw [key_count_map] at hr
    have hrmem : r ∈ Multiset.map δ' (Finset.univ : Finset (Fin D)).val :=
      Multiset.count_ne_zero.mp hr
    rw [Multiset.mem_map] at hrmem
    obtain ⟨i, hi, hir⟩ := hrmem
    simpa [← hir] using hδ'M i
  let p : Fin M → Fin (D + 1) :=
    boundedPatternOfFinsupp (key δ') D M hkeyCount
  have hpcount : (∑ j, (p j : ℕ)) = D := by
    exact boundedPatternOfFinsupp_count (key δ') D M hkeyCount hkeySupp
  let g : Fin D → Fin M := fun i => ⟨δ' i, hδ'M i⟩
  have hg : g ∈ atomPatternAssignments p := by
    rw [mem_atomPatternAssignments]
    change key δ' = atomPatternKey p
    exact (atomPatternKey_boundedPatternOfFinsupp
      (key δ') D M hkeyCount hkeySupp).symm
  let Q₀ := Qbal + K
  refine ⟨K, M, p, Q₀, by simpa [D] using hpcount, ?_⟩
  intro q hq
  let qraw := q - K
  have hKq : K ≤ q := (Nat.le_add_left K Qbal).trans hq
  have hqraw : Qbal ≤ qraw := by dsimp [qraw]; omega
  have hrawK : qraw + K = q := by dsimp [qraw]; omega
  have hold : Qbal ≤ qraw + J := hqraw.trans (Nat.le_add_right _ _)
  have hdata := hbalanced (qraw + J) hold
  let sOld : Fin D → ℕ := fun i => (qraw + J) + δ i
  let NOld := (∑ i, sOld i) + anchor 0 - J
  have hNOld : NOld = D * q + τ := by
    have hshape : NOld = D * qraw + C₀ := by
      simpa only [sOld, NOld] using hNshape qraw
    rw [hshape, ← hC₀shape, ← hrawK]
    ring
  have hsEq : sOld = fun i => windowShift q K (g i : ℕ) := by
    funext i
    dsimp [sOld, g, δ', windowShift]
    omega
  have hkeyEq : key sOld = shiftedAtomPatternKey q K p := by
    rw [hsEq]
    exact key_windowShift_eq_shiftedAtomPatternKey p g hg
  have hmem : key sOld ∈ (sigmaIdx n NOld Q).image (atomKeyOf n) := by
    simpa only [D, J, sOld, NOld] using hdata.2.1
  have hweight : aevalWeight n NOld Q (key sOld) ≠ 0 := by
    simpa only [D, J, sOld, NOld] using hdata.2.2.1
  constructor
  · simpa [hNOld, hkeyEq] using hmem
  · simpa [hNOld, hkeyEq] using hweight

end

end GaloisForLFunctions
