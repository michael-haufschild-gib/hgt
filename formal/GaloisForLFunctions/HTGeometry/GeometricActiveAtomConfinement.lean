import GaloisForLFunctions.HTGeometry.GeometricFaceNormalizedWeight
import GaloisForLFunctions.HTGeometry.HierarchicalResonanceBreaking
import GaloisForLFunctions.HTGeometry.PolynomialPhaseLockAssembly

/-!
# Active-atom confinement for geometric Taylor profiles

An eventual geometric lower step turns one fixed translated top-degree pattern into a uniform
confinement scale.  Every active atom lying less than one full geometric step above that witness
has top degree and is supported in one fixed translated window.
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries MvPolynomial Topology

noncomputable section

/-- Every bounded multiplicity pattern of total count `D` admits a labelled assignment of its
`D` copies to the occupied offsets. -/
theorem atomPatternAssignments_nonempty_of_count
    {M D : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    (atomPatternAssignments p).Nonempty := by
  classical
  let ν := atomPatternKey p
  have hνcount : ν.sum (fun _ k => k) = D := by
    exact (atomPatternKey_count p).trans hcount
  let s := tupleOfFinsupp ν D hνcount
  have hkey : key s = shiftedAtomPatternKey 0 0 p := by
    rw [key_tupleOfFinsupp ν D hνcount]
    rw [shiftedAtomPatternKey_eq_sum]
    simp only [windowShift, zero_tsub, zero_add]
    rfl
  obtain ⟨g, hg, _hunique⟩ :=
    existsUnique_atomPatternAssignment_of_key_eq_shifted p s hkey
  exact ⟨g, hg.1⟩

/-- Canonical labelled realization of a bounded multiplicity pattern. -/
noncomputable def canonicalAtomPatternAssignment
    {M D : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) : Fin D → Fin M :=
  (atomPatternAssignments_nonempty_of_count p hcount).choose

theorem canonicalAtomPatternAssignment_mem
    {M D : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    canonicalAtomPatternAssignment p hcount ∈ atomPatternAssignments p :=
  (atomPatternAssignments_nonempty_of_count p hcount).choose_spec

/-- Largest occupied labelled offset of the canonical realization. -/
noncomputable def atomPatternMaxOffset
    {M D : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) : ℕ :=
  magnitudeOffsetMax fun i => (canonicalAtomPatternAssignment p hcount i : ℕ)

/-- A fixed translated top-degree witness controls every active atom within one geometric
valuation step.  The conclusion is a two-sided window about the witness's translation base
`q - K₀`, with radius independent of `q`. -/
theorem exists_eventually_activeAtom_geometricWitness_window
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    (hgrowth : UniformGeometricGrowth b)
    {n D K₀ τ M : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) :
    ∃ R : ℕ, ∀ᶠ q : ℕ in atTop,
      ∀ ν ∈ activeAevalAtoms n (D * q + τ) Q,
        atomValuation b ν <
            atomValuation b (shiftedAtomPatternKey q K₀ p) +
              b (q - K₀ + atomPatternMaxOffset p hcount) →
          ν.sum (fun _ k => k) = D ∧
            ∀ i, ν i ≠ 0 →
              q - K₀ - R ≤ i ∧ i ≤ q - K₀ + R := by
  classical
  obtain ⟨r, Ntail, hr1, hlower⟩ := hgrowth
  let g : Fin D → Fin M :=
    canonicalAtomPatternAssignment p hcount
  have hg : g ∈ atomPatternAssignments p :=
    canonicalAtomPatternAssignment_mem p hcount
  let δ : Fin D → ℕ := fun i => (g i : ℕ)
  let B := magnitudeOffsetMax δ
  obtain ⟨L, hL⟩ : ∃ L : ℕ, (D : ℝ) + 1 < r ^ L :=
    (tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_gt_atTop ((D : ℝ) + 1) |>.exists
  let J := magnitudeMaxJetOrder n Q
  let Z := magnitudeMaxXDegree Q
  let R := D * (B + L) + J + Z
  refine ⟨R, ?_⟩
  filter_upwards [eventually_ge_atTop (max K₀
    (K₀ + max Ntail
      (max (max (2 * (J + Z) + 2) (2 * D * (B + L))) R))),
    eventually_ge_atTop (Z + 1)] with q hq hqZ
  intro ν hν hnear
  have hK₀q : K₀ ≤ q := (le_max_left _ _).trans hq
  let q₀ := q - K₀
  have hq₀tail : Ntail ≤ q₀ := by
    dsimp [q₀]
    omega
  have hq₀threshold :
      max (2 * (J + Z) + 2) (2 * D * (B + L)) ≤ q₀ := by
    dsimp [q₀]
    omega
  have hq₀R : R ≤ q₀ := by
    dsimp [q₀]
    omega
  have hNZ : Z < D * q + τ := by
    have hDq : q ≤ D * q := by
      simpa [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ D by omega)
    omega
  have hDqN : D * q₀ ≤ D * q + τ + J := by
    have hsub := Nat.mul_le_mul_left D (Nat.sub_le q K₀)
    dsimp [q₀]
    omega
  have hνappears : ν ∈ (sigmaIdx n (D * q + τ) Q).image (atomKeyOf n) :=
    (mem_activeAevalAtoms.mp hν).1
  have hwitness :
      key (fun i : Fin D => q₀ + δ i) =
        shiftedAtomPatternKey q K₀ p := by
    simpa [q₀, δ, windowShift] using
      key_windowShift_eq_shiftedAtomPatternKey p g hg
  let P : ℝ := Real.exp (b (q₀ + B)) - 1
  have hlog : Real.log (P + 1) ≤ b (q₀ + B) := by
    have : P + 1 = Real.exp (b (q₀ + B)) := by dsimp [P]; ring
    rw [this, Real.log_exp]
  have hnear' :
      ν.sum (fun i k => (k : ℝ) * b i) <
        (key (fun i : Fin D => q₀ + δ i)).sum
            (fun i k => (k : ℝ) * b i) + Real.log (P + 1) := by
    rw [hwitness]
    have hlogEq : Real.log (P + 1) = b (q₀ + B) := by
      have : P + 1 = Real.exp (b (q₀ + B)) := by dsimp [P]; ring
      rw [this, Real.log_exp]
    simpa [atomValuation, q₀, B, δ, g, atomPatternMaxOffset, hlogEq] using hnear
  have hconf := near_balanced_atom_count_eq_and_supportMax_lt_of_geometric_lower
    hbpos hr1 hlower Q hD hDmax δ hνappears hnear' hlog hDqN hNZ
      hq₀tail hq₀threshold hL
  have hmax :
      ν.support.max' (appearing_atom_support_nonempty_of_maxX_lt_level Q hνappears hNZ) <
        q₀ + (B + L) := by
    have hmax' := hconf.2
    dsimp [B] at hmax' ⊢
    simpa only [Nat.add_assoc] using hmax'
  have hwindow := appearing_topDegree_support_window Q hD hνappears hconf.1
    hDqN hNZ hmax hq₀R
  refine ⟨hconf.1, ?_⟩
  simpa [q₀, R] using hwindow

/-- Near-witness active atoms are exactly translated bounded patterns in one fixed finite window. -/
theorem exists_eventually_activeAtom_geometricWitness_pattern
    {b : ℕ → ℝ} (hbpos : ∀ i, 0 < b i)
    (hgrowth : UniformGeometricGrowth b)
    {n D K₀ τ M₀ : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hD : 0 < D) (hDmax : D = magnitudeMaxJetDegree n Q)
    (p₀ : Fin M₀ → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D) :
    ∃ K M : ℕ, K₀ ≤ K ∧ ∀ᶠ q : ℕ in atTop,
      ∀ ν ∈ activeAevalAtoms n (D * q + τ) Q,
        atomValuation b ν <
            atomValuation b (shiftedAtomPatternKey q K₀ p₀) +
              b (q - K₀ + atomPatternMaxOffset p₀ hcount₀) →
          ∃ p : Fin M → Fin (D + 1),
            (∑ r, (p r : ℕ)) = D ∧ shiftedAtomPatternKey q K p = ν := by
  obtain ⟨R, hR⟩ := exists_eventually_activeAtom_geometricWitness_window
    hbpos hgrowth Q hD hDmax p₀ hcount₀
  let K := K₀ + R
  let M := 2 * R + 1
  refine ⟨K, M, by simp [K], ?_⟩
  filter_upwards [hR, eventually_ge_atTop K] with q hRq hKq
  intro ν hν hnear
  have hdata := hRq ν hν hnear
  have hsupp : ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i < q - K + M := by
    intro i hi
    have hi' := hdata.2 i hi
    dsimp [K, M]
    omega
  exact exists_boundedPattern_of_atom_support_interval hKq ν hdata.1 hsupp

end

end GaloisForLFunctions
