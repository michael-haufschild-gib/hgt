import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierAdaptiveMixedCompletedSource

/-!
# All-contact residue of the strict-frontier arithmetic source wall

At every occupied strict shifted-Xi frontier, the first live Padé contact has finite order `d`.
The newborn canonical admission norm vanishes to exactly that order, with positive coefficient.
The preceding adaptive arithmetic source remains continuous and strictly positive.  Therefore the
actual Christoffel source wall has one exact finite positive residue after multiplication by the
intrinsic distance power `d`.

This replaces the simple/double/infinite-under-fixed-scaling trichotomy by a single all-contact
law.  On the physical germ, the wall is literally the current adaptive mixed completed
rational--Gamma-minus-von-Mangoldt source divided by the newborn admission norm.  No orientation
map, fixed reporter, numerical estimate, or RH premise enters.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

noncomputable section

/-- Positive leading coefficient of the newborn admission norm at contact order `d`. -/
noncomputable def xiShiftedStrictFrontierAdmissionNormContactCoefficient
    (n d : ℕ) : ℝ :=
  (-1 : ℝ) ^ d * (Nat.choose (2 * (n + 2) + d) d : ℝ) *
    xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)

/-- Intrinsic all-order residue of the preceding Christoffel source wall. -/
noncomputable def xiShiftedStrictFrontierAllContactSourceWallResidue
    (n d : ℕ) : ℝ :=
  xiShiftedCanonicalAdmissionAdaptiveShear
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) /
    (16 * xiShiftedStrictFrontierAdmissionNormContactCoefficient n d)

/-- Christoffel source wall scaled by its exact first contact order. -/
noncomputable def xiShiftedStrictFrontierAllContactScaledSourceWall
    (n d : ℕ) (u : ℝ) : ℝ :=
  u ^ d * xiShiftedCanonicalAdmissionChristoffelSourceWall
    (xiShiftedHigherBlockTerminalFrontier (n + 1) + u) (n + 1)

/-- Literal current adaptive mixed completed arithmetic-source wall, scaled by first contact
order.  Admission and source formation both occur at the displaced mass before the quotient. -/
noncomputable def xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall
    (n d : ℕ) (u : ℝ) : ℝ :=
  let v := xiShiftedHigherBlockTerminalFrontier (n + 1) + u
  u ^ d *
    (xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt v)
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence (Real.sqrt v)) (n + 1)) /
      (32 * xiShiftedCanonicalAdmissionNorm v (n + 2)))

theorem xiShiftedStrictFrontierAdmissionNormContactCoefficient_pos
    {n d : ℕ}
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    0 < xiShiftedStrictFrontierAdmissionNormContactCoefficient n d := by
  have hchooseNat : 0 < Nat.choose (2 * (n + 2) + d) d :=
    Nat.choose_pos (by omega)
  have hchoose : 0 < (Nat.choose (2 * (n + 2) + d) d : ℝ) := by
    exact_mod_cast hchooseNat
  rw [xiShiftedStrictFrontierAdmissionNormContactCoefficient]
  calc
    (-1 : ℝ) ^ d * (Nat.choose (2 * (n + 2) + d) d : ℝ) *
        xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d) =
      (Nat.choose (2 * (n + 2) + d) d : ℝ) *
        ((-1 : ℝ) ^ d *
          xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) := by ring
    _ > 0 := mul_pos hchoose hsigned

/-- **Exact all-contact Christoffel source-wall residue.**  If `d` is the first live canonical
Padé contact, multiplication by distance to power `d` converts the actual source wall to one
finite positive residue. -/
theorem tendsto_xiShiftedStrictFrontierAllContactScaledSourceWall
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    Tendsto (xiShiftedStrictFrontierAllContactScaledSourceWall n d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let source : ℝ → ℝ := fun v =>
    xiShiftedCanonicalAdmissionAdaptiveShear v (n + 1)
  let N : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (n + 2)
  let C := xiShiftedStrictFrontierAdmissionNormContactCoefficient n d
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hhead : (xiShiftedMomentHankelMatrix y (n + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hsourceCont : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy (n + 1) (ne_of_gt hhead.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using h
  have hsourceTendsto : Tendsto (fun u : ℝ => source (y + u) / 16)
      (𝓝[>] (0 : ℝ)) (𝓝 (source y / 16)) := by
    have hadd : Tendsto (fun u : ℝ => y + u) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
      have hfull : Tendsto (fun u : ℝ => y + u) (𝓝 (0 : ℝ)) (𝓝 y) := by
        have hc : Tendsto (fun _u : ℝ => y) (𝓝 (0 : ℝ)) (𝓝 y) :=
          tendsto_const_nhds
        have hi : Tendsto (fun u : ℝ => u) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) :=
          tendsto_id
        simpa using hc.add hi
      exact hfull.mono_left nhdsWithin_le_nhds
    exact (hsourceCont.tendsto.comp hadd).div_const 16
  have hN : Tendsto (fun u : ℝ => N (y + u) / u ^ d)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    simpa only [N, y, C, xiShiftedStrictFrontierAdmissionNormContactCoefficient] using
      tendsto_xiShiftedStrictFrontierAdmissionNorm_div_pow_at_contact
        hne hstrict hd hzero
  have hC : 0 < C := by
    simpa only [C] using
      xiShiftedStrictFrontierAdmissionNormContactCoefficient_pos hsigned
  have hInv : Tendsto (fun u : ℝ => (N (y + u) / u ^ d)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 C⁻¹) := hN.inv₀ hC.ne'
  have hprod : Tendsto
      (fun u : ℝ => source (y + u) / 16 * (N (y + u) / u ^ d)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (source y / (16 * C))) := by
    convert hsourceTendsto.mul hInv using 1
    field_simp [hC.ne']
  have hNpos := eventually_pos_xiShiftedCanonicalAdmissionNorm_add_at_strict_frontier
    hne hstrict
  apply hprod.congr'
  filter_upwards [hNpos, self_mem_nhdsWithin] with u hNu hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hNu0 : N (y + u) ≠ 0 := by simpa only [N, y] using ne_of_gt hNu
  dsimp only [xiShiftedStrictFrontierAllContactScaledSourceWall,
    xiShiftedCanonicalAdmissionChristoffelSourceWall,
    xiShiftedStrictFrontierAllContactSourceWallResidue, source, N, C, y]
  field_simp

/-- Exact all-contact residue is strictly positive. -/
theorem xiShiftedStrictFrontierAllContactSourceWallResidue_pos
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    0 < xiShiftedStrictFrontierAllContactSourceWallResidue n d := by
  have hsource :=
    xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  have hC := xiShiftedStrictFrontierAdmissionNormContactCoefficient_pos hsigned
  rw [xiShiftedStrictFrontierAllContactSourceWallResidue]
  exact div_pos hsource (mul_pos (by norm_num) hC)

/-- On every physical strict-frontier germ, intrinsic scaled Christoffel wall is eventually equal
to literal current adaptive mixed completed arithmetic-source wall. -/
theorem eventuallyEq_xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall
    {n d : ℕ}
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall n d =ᶠ[𝓝[>] (0 : ℝ)]
      xiShiftedStrictFrontierAllContactScaledSourceWall n d := by
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 < u at hu
  have hv : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) + u := by
    linarith
  rw [xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall,
    xiShiftedStrictFrontierAllContactScaledSourceWall,
    xiShiftedCanonicalAdmissionChristoffelSourceWall_eq_arithmeticSource_div hv]

/-- Literal arithmetic-source version of exact all-contact residue. -/
theorem tendsto_xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall
    {n d : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hd : 0 < d)
    (hzero : ∀ k < 2 * (n + 2) + d,
      xiShiftedStrictFrontierPadeDefect n k = 0)
    (hsigned : 0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d)) :
    Tendsto (xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall n d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) := by
  exact (tendsto_xiShiftedStrictFrontierAllContactScaledSourceWall
    hne hstrict hd hzero hsigned).congr'
      (eventuallyEq_xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall
        hphysical).symm

/-- Complete intrinsic all-contact wall law at one strict frontier. -/
def XiShiftedStrictFrontierAllContactSourceWallResidueLaw (n : ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧
    (∀ k < 2 * (n + 2) + d, xiShiftedStrictFrontierPadeDefect n k = 0) ∧
    0 < (-1 : ℝ) ^ d *
      xiShiftedStrictFrontierPadeDefect n (2 * (n + 2) + d) ∧
    0 < xiShiftedStrictFrontierAllContactSourceWallResidue n d ∧
    Tendsto (xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall n d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (xiShiftedStrictFrontierAllContactSourceWallResidue n d)) ∧
    XiShiftedAdaptiveMixedCompletedFirstContactSourceLaw
      (Real.sqrt (xiShiftedHigherBlockTerminalFrontier (n + 1))) (n + 2) d
      (xiShiftedStrictFrontierNullVector n)

/-- Every occupied physical strict frontier has an exact finite positive intrinsic arithmetic
source-wall residue at its finite first contact. -/
theorem xiShiftedStrictFrontier_allContactSourceWallResidueLaw
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    XiShiftedStrictFrontierAllContactSourceWallResidueLaw n := by
  have hcontact := xiShiftedStrictFrontier_adaptiveMixedCompletedContactLaw
    hne hstrict hphysical
  dsimp only [XiShiftedStrictFrontierAdaptiveMixedCompletedContactLaw] at hcontact
  obtain ⟨d, hd, hzero, hsigned, hsource⟩ := hcontact
  refine ⟨d, hd, hzero, hsigned,
    xiShiftedStrictFrontierAllContactSourceWallResidue_pos hne hstrict hsigned,
    tendsto_xiShiftedStrictFrontierAllContactScaledArithmeticSourceWall
      hne hstrict hphysical hd hzero hsigned,
    hsource⟩

/-- False-RH alternative in exact intrinsic arithmetic source-wall residue coordinates. -/
def XiShiftedCofinalAllContactSourceWallResiduePhase : Prop :=
  ∀ A : ℝ, ∃ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty ∧
      A < xiShiftedHigherBlockTerminalFrontier n ∧
      xiShiftedHigherBlockTerminalFrontier n <
        xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
      XiShiftedStrictFrontierAllContactSourceWallResidueLaw n

theorem xiShiftedCofinalAllContactSourceWallResiduePhase_of_not_riemannHypothesis
    (hnot : ¬RiemannHypothesis) :
    XiShiftedCofinalAllContactSourceWallResiduePhase := by
  intro A
  obtain ⟨n, hne, hA, hstrict, _⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnot
      (max A (1 / 4))
  have hA' : A < xiShiftedHigherBlockTerminalFrontier n :=
    lt_of_le_of_lt (le_max_left _ _) hA
  have hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1) :=
    lt_trans (lt_of_le_of_lt (le_max_right _ _) hA) hstrict
  exact ⟨n, hne, hA', hstrict, hphysical,
    xiShiftedStrictFrontier_allContactSourceWallResidueLaw hne hstrict hphysical⟩

theorem not_xiShiftedCofinalAllContactSourceWallResiduePhase_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ¬XiShiftedCofinalAllContactSourceWallResiduePhase := by
  intro hphase
  obtain ⟨n, hne, _⟩ := hphase 0
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- Premise-free phase closure after exact all-contact wall quotient. -/
theorem riemannHypothesis_iff_not_xiShiftedCofinalAllContactSourceWallResiduePhase :
    RiemannHypothesis ↔ ¬XiShiftedCofinalAllContactSourceWallResiduePhase := by
  constructor
  · exact not_xiShiftedCofinalAllContactSourceWallResiduePhase_of_riemannHypothesis
  · intro hnotPhase
    by_contra hnotRH
    exact hnotPhase
      (xiShiftedCofinalAllContactSourceWallResiduePhase_of_not_riemannHypothesis hnotRH)

end

end RHTower
