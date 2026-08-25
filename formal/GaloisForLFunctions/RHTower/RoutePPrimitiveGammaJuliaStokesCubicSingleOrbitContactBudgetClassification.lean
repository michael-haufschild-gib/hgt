import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicMicrolocalWittSignatureRigidity

/-!
# Cubic Xi global single-orbit contact-budget classification

For arbitrary genus, any nonempty marked-point family with exactly one Stokes orbit at every
point has a complete unit-Rees landing phase diagram.  Its topology, branch multiplicities, and
ordered normalized Puiseux contacts combine into one scalar coefficient `A`, and every compatible
charge satisfies

`W = A * rank²`.

Consequently the negative completed-Xi cubic Malgrange residual lands exactly when `A < 0`.
The converse is constructive: one common square-root rank determines the unique local orbit charge
at every point.  This exhausts the abstract coefficient-generated single-orbit receiver sector.

No arithmetic source-to-charge map or meromorphic-connection existence statement is asserted.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

/-- Ordered normalized Puiseux contact mass at one coefficient-generated single-orbit point. -/
noncomputable def routePPrimitiveGammaJuliaStokesSingleOrbitContactBudget
    {m K N : ℕ} (d : PuiseuxOrbitCoareaDatum 1 m K N) : ℝ :=
  ∑ i, ∑ j, d.branches.contactNumerator i j / (N : ℝ)

/-- Exact common-rank-square coefficient for an arbitrary global single-orbit unit-Rees system. -/
noncomputable def routePPrimitiveGammaJuliaStokesSingleOrbitUnitCoefficient
    {p : ℕ} {m K N : Fin (p + 1) → ℕ}
    (genus : ℕ) (d : LocalData p (fun _ => 1) m K N) : ℝ :=
  fusionCoefficient genus (p + 1) +
    ∑ a, (1 + (m a : ℝ) ^ 2 -
      routePPrimitiveGammaJuliaStokesSingleOrbitContactBudget (d a)) / (m a : ℝ) ^ 2

private theorem singleOrbit_branchCount_pos
    {m K N : ℕ} (d : PuiseuxOrbitCoareaDatum 1 m K N) :
    0 < m := by
  obtain ⟨i, _⟩ := d.orbit_surjective 0
  exact lt_of_le_of_lt (Nat.zero_le i.val) i.isLt

private theorem singleOrbit_localRank_eq_branchCount_mul
    {m K N : ℕ} (d : PuiseuxOrbitCoareaDatum 1 m K N) (x : Fin 1 → ℝ) :
    localRankLinear d x = (m : ℝ) * x 0 := by
  have horbit : ∀ i : Fin m, d.toOrbitCoareaDatum.orbit i = 0 := by
    intro i
    change d.orbit i = 0
    exact Subsingleton.elim _ _
  simp [localRankLinear_apply, OrbitCoareaDatum.physicalRank,
    OrbitCoareaDatum.liftCharge, horbit, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

private theorem singleOrbit_localWittForm_eq_contactBudget
    {m K N : ℕ} (d : PuiseuxOrbitCoareaDatum 1 m K N) (x : Fin 1 → ℝ) :
    localWittForm d x =
      (1 + (m : ℝ) ^ 2 -
        routePPrimitiveGammaJuliaStokesSingleOrbitContactBudget d) * x 0 ^ 2 := by
  have horbit : ∀ i : Fin m, d.toOrbitCoareaDatum.orbit i = 0 := by
    intro i
    change d.orbit i = 0
    exact Subsingleton.elim _ _
  have hcontact : ∀ i j : Fin m,
      d.toOrbitCoareaDatum.cuts.contact i j =
        d.branches.contactNumerator i j / (N : ℝ) := by
    intro i j
    change d.branches.canonicalCuts.contact i j = _
    exact d.branches.canonicalCuts_contact_eq i j
  have hpair : d.toOrbitCoareaDatum.contactPairing x =
      routePPrimitiveGammaJuliaStokesSingleOrbitContactBudget d * x 0 ^ 2 := by
    simp only [OrbitCoareaDatum.contactPairing, OrbitCoareaDatum.liftCharge, horbit,
      hcontact, routePPrimitiveGammaJuliaStokesSingleOrbitContactBudget]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [localWittForm_apply, OrbitCoareaDatum.cartanQuadratic, hpair]
  simp only [OrbitCoareaDatum.terminalEnergy, Fin.sum_univ_one,
    OrbitCoareaDatum.physicalRank, OrbitCoareaDatum.liftCharge, horbit,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Exact global contact law: every unit-Rees compatible charge in the single-orbit sector lies on
one common-rank square with explicitly computed topology/contact coefficient. -/
theorem routePPrimitiveGammaJuliaStokesSingleOrbitUnitWittForm_contactBudgetLaw
    {p : ℕ} {m K N : Fin (p + 1) → ℕ}
    (genus : ℕ) (d : LocalData p (fun _ => 1) m K N)
    (x : compatibleCharges d) :
    globalReesWittForm genus d (fun _ _ => 1) x =
      routePPrimitiveGammaJuliaStokesSingleOrbitUnitCoefficient genus d *
        commonRankLinear d x ^ 2 := by
  have hmpos : ∀ a, 0 < m a := fun a => singleOrbit_branchCount_pos (d a)
  have hmne : ∀ a, (m a : ℝ) ≠ 0 := by
    intro a
    exact_mod_cast (ne_of_gt (hmpos a))
  have hcoordinate : ∀ a, x.1 a 0 = commonRankLinear d x / (m a : ℝ) := by
    intro a
    have hrank := compatible_localRank d x a
    rw [singleOrbit_localRank_eq_branchCount_mul] at hrank
    rw [← hrank]
    field_simp [hmne a]
  have hlocal : ∀ a,
      (1 + (m a : ℝ) ^ 2 -
          routePPrimitiveGammaJuliaStokesSingleOrbitContactBudget (d a)) *
          (commonRankLinear d x / (m a : ℝ)) ^ 2 =
        ((1 + (m a : ℝ) ^ 2 -
          routePPrimitiveGammaJuliaStokesSingleOrbitContactBudget (d a)) /
            (m a : ℝ) ^ 2) * commonRankLinear d x ^ 2 := by
    intro a
    field_simp [hmne a]
  rw [globalReesWittForm_one, globalWittForm, QuadraticMap.add_apply,
    QuadraticMap.sum_apply, QuadraticMap.smul_apply, QuadraticMap.comp_apply,
    QuadraticMap.sq_apply]
  simp only [smul_eq_mul]
  simp_rw [QuadraticMap.comp_apply, localProjection_apply,
    singleOrbit_localWittForm_eq_contactBudget, hcoordinate, hlocal]
  rw [routePPrimitiveGammaJuliaStokesSingleOrbitUnitCoefficient, ← Finset.sum_mul]
  ring

/-- Every global single-orbit cubic landing has the exact common-rank magnitude dictated by the
negative contact-budget chamber. -/
theorem routePPrimitiveGammaJuliaStokesCubicSingleOrbitUnitLanding_chargeMagnitude
    {p : ℕ} {m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p (fun _ => 1) m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1)) :
    (-routePPrimitiveGammaJuliaStokesSingleOrbitUnitCoefficient genus d) *
        commonRankLinear d x.1 ^ 2 =
      -(normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) := by
  have hlaw :=
    routePPrimitiveGammaJuliaStokesSingleOrbitUnitWittForm_contactBudgetLaw genus d x.1
  rw [x.2] at hlaw
  linarith

/-- **Complete global single-orbit landing phase diagram.**  Arbitrary topology, ramification, and
coefficient contacts carry the negative completed-Xi cubic residual exactly when their explicit
unit common-rank coefficient is negative. -/
theorem nonempty_routePPrimitiveGammaJuliaStokesCubicSingleOrbitUnitLandingFiber_iff_coefficient_neg
    {p : ℕ} {m K N : Fin (p + 1) → ℕ}
    (genus : ℕ) (d : LocalData p (fun _ => 1) m K N) :
    Nonempty (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      genus d (fun _ _ => 1)) ↔
      routePPrimitiveGammaJuliaStokesSingleOrbitUnitCoefficient genus d < 0 := by
  constructor
  · rintro ⟨x⟩
    have hlaw :=
      routePPrimitiveGammaJuliaStokesSingleOrbitUnitWittForm_contactBudgetLaw genus d x.1
    rw [x.2] at hlaw
    have htarget := normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg
    by_contra hcoefficient
    push Not at hcoefficient
    have hnonneg :
        0 ≤ routePPrimitiveGammaJuliaStokesSingleOrbitUnitCoefficient genus d *
          commonRankLinear d x.1 ^ 2 :=
      mul_nonneg hcoefficient (sq_nonneg _)
    linarith
  · intro hcoefficient
    let target : ℝ :=
      normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4
    let A : ℝ := routePPrimitiveGammaJuliaStokesSingleOrbitUnitCoefficient genus d
    let r : ℝ := Real.sqrt ((-target) / (-A))
    let raw : GlobalCharge p (fun _ => 1) := fun a _ => r / (m a : ℝ)
    have hmpos : ∀ a, 0 < m a := fun a => singleOrbit_branchCount_pos (d a)
    have hmne : ∀ a, (m a : ℝ) ≠ 0 := by
      intro a
      exact_mod_cast (ne_of_gt (hmpos a))
    have hraw : ∀ a,
        localRankLinear (d a) (raw a) = localRankLinear (d 0) (raw 0) := by
      intro a
      rw [singleOrbit_localRank_eq_branchCount_mul,
        singleOrbit_localRank_eq_branchCount_mul]
      dsimp [raw]
      field_simp [hmne a, hmne 0]
    let y : compatibleCharges d := ⟨raw, hraw⟩
    have htarget : target < 0 := by
      exact normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg
    have hA : A < 0 := by
      exact hcoefficient
    have hquot : 0 ≤ (-target) / (-A) :=
      div_nonneg (neg_nonneg.mpr htarget.le) (neg_nonneg.mpr hA.le)
    have hr_sq : r ^ 2 = (-target) / (-A) := by
      dsimp [r]
      exact Real.sq_sqrt hquot
    have hyrank : commonRankLinear d y = r := by
      rw [commonRankLinear_apply, singleOrbit_localRank_eq_branchCount_mul]
      dsimp [y, raw]
      field_simp [hmne 0]
    refine ⟨⟨y, ?_⟩⟩
    rw [routePPrimitiveGammaJuliaStokesSingleOrbitUnitWittForm_contactBudgetLaw,
      hyrank, hr_sq]
    change A * ((-target) / (-A)) = target
    field_simp [hA.ne]

end

end RHTower
