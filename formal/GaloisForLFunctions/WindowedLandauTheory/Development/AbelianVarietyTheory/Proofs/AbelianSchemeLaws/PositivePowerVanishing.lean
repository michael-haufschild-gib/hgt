import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SerreVanishingPowerProgression
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalPowerBundleIso
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.KernelAverageCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TorsionSectionDecomposition

/-! Positive powers of a symmetric ample bundle have zero higher cohomology.
Pullback by a large prime-to-characteristic multiplication map reaches the
Serre-vanishing range, and normalized trace descends exactness. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj TopologicalSpace HTGeometry
open GlobalTheory.CommPairing GlobalTheory.FlatDescent GlobalTheory.LineBundleSections
open GlobalTheory.ProjectiveSections GlobalTheory.SchemeCohomology UpperTheory.Cb
open GlobalTheory.TwistTranslate
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

open GrpTangent (mulN comp_mulN finiteEtaleSurjective_mulN isMonHom_mulN)

private theorem exists_large_admissible_square (K : Type) [Field K] (N j : ℕ) (hj : 1 ≤ j) (b : ℤ) :
    ∃ m t : ℕ, (m : K) ≠ 0 ∧ b ≤ (t : ℤ) ∧
      (m : ℤ) ^ 2 * (j : ℤ) = (j : ℤ) + (N : ℤ) * (t : ℤ) := by
  let C := max 1 (ringChar K)
  let B := C * (b.toNat + 1)
  let m := N * B + 1
  let t := B * (N * B + 2) * j
  have hC : 1 ≤ C := le_max_left _ _
  have hB : b.toNat + 1 ≤ B := Nat.le_mul_of_pos_left _ hC
  have ht : B ≤ t :=
    (Nat.le_mul_of_pos_right B (by omega : 0 < N * B + 2)).trans (Nat.le_mul_of_pos_right _ hj)
  refine ⟨m, t, ?_, (Int.self_le_toNat b).trans (Int.ofNat_le.mpr (by omega : b.toNat ≤ t)), ?_⟩
  · by_cases hc : ringChar K = 0
    · intro hz
      have h := (ringChar.spec K m).mp hz
      rw [hc, zero_dvd_iff] at h
      exact Nat.succ_ne_zero _ h
    · have hcast : (C : K) = 0 := by
        dsimp only [C]
        rw [max_eq_right (Nat.pos_of_ne_zero hc)]
        exact (ringChar.spec K _).mpr dvd_rfl
      simp only [m, B, Nat.cast_add, Nat.cast_one, Nat.cast_mul, hcast, zero_mul, mul_zero, zero_add]
      exact (one_ne_zero : (1 : K) ≠ 0)
  · dsimp only [m, t]
    push_cast
    ring

/-- Every positive power of a symmetric rigidified ample bundle on an abelian
variety over an algebraically closed field has vanishing higher cohomology. -/
theorem cohomology_positive_power_subsingleton {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of K), ∃ U : (Spec (.of K)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (j : ℕ) (hj : 1 ≤ j) (n : ℕ) :
    Subsingleton (CohomologyOn
      (toMod (LB.LinComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (j : ℤ)))) ⊤ (n + 1)) := by
  letI := hA.comm
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  letI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  obtain ⟨N, -, b, hb⟩ := exists_cohomology_vanishing_progression hL hAmp (j : ℤ)
  obtain ⟨m, t, hm, ht, hmt⟩ := exists_large_admissible_square K N j hj b
  let Z := 𝟙_ (Over (Spec (.of K)))
  let G := (powMonoidHom m : (Z ⟶ A) →* (Z ⟶ A)).ker
  let q := mulN A m
  letI : Finite G := finite_prime_to_char_torsion hA m hm
  letI : Fintype G := Fintype.ofFinite G
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  have hunit : IsUnit (m : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using (Ne.isUnit hm).map e.toRingHom
  obtain ⟨hfin, het, hsur⟩ := finiteEtaleSurjective_mulN A hunit
  letI : IsFinite q.left := hfin
  letI : Etale q.left := het
  letI : Surjective q.left := hsur
  letI : IsMonHom q := isMonHom_mulN A m
  let τ (y : G) : A ⟶ A := translate A y.1
  have hτq (y : G) : τ y ≫ q = q := by
    change translate A y.1 ≫ mulN A m = mulN A m
    rw [translate_comp_mulN, show y.1 ^ m = 1 from y.2, translate_one, Category.comp_id]
  have hτ (y : G) : (τ y).left ≫ q.left = q.left := congrArg Over.Hom.left (hτq y)
  have hmul (x y : G) : (τ x).left ≫ (τ y).left = (τ (x * y)).left :=
    congrArg Over.Hom.left ((translate_comp x.1 y.1).trans (congrArg (translate A) (mul_comm y.1 x.1)))
  have hD : Descends q.left (fun y : G => (τ y).left) := by
    have H := descends_of_etale_isogeny q
    refine ⟨H.1, fun U v hv => H.2 U v fun y => ?_⟩
    exact hv ⟨y.1, (comp_mulN y.1 m).symm.trans y.2⟩
  have hdvd : Fintype.card G ∣ m ^ Group.rank G := by
    simpa only [Nat.card_eq_fintype_card] using
      card_dvd_exponent_pow_rank' G (fun y : G => Subtype.ext y.2)
  have hcard : IsUnit (Fintype.card G : Γ(A.left, ⊤)) := by
    have hmu := hunit.map A.hom.appTop.hom
    rw [map_natCast] at hmu
    have hdiv : (Fintype.card G : Γ(A.left, ⊤)) ∣ (m : Γ(A.left, ⊤)) ^ Group.rank G := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : Γ(A.left, ⊤)), ?_⟩
      have e := congrArg (fun v : ℕ => (v : Γ(A.left, ⊤))) hc
      simpa only [Nat.cast_mul, Nat.cast_pow] using e
    exact isUnit_of_dvd_unit hdiv (hmu.pow _)
  let M := LB.LinComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (j : ℤ))
  let B := LB.LinComb L (fun _ : PUnit => q.left) (fun _ => (j : ℤ))
  let P := LB.LinComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (m : ℤ) ^ 2 * (j : ℤ))
  have hM : M.IsLB := hL.linComb _ _
  have hB : B.IsLB := hL.linComb _ _
  have hP : P.IsLB := hL.linComb _ _
  obtain ⟨α, hα⟩ := AbLaw.Cube.gen_mul_pullback_of_relAmple hA hL hAmp hrig hsym m
  obtain ⟨β, hβ⟩ := exists_gen_scaled hα j
  have hpow : (fun i : Fin 2 => (![(m : ℤ) ^ 2, -1] : Fin 2 → ℤ) i * (j : ℤ)) =
      ![(m : ℤ) ^ 2 * (j : ℤ), -(j : ℤ)] := by
    funext i
    fin_cases i <;> simp
  have hiso : ∃ z : LB.Iso B P, z.IsGen := by
    have hz : ∃ c : (LB.LinComb L ![𝟙 A.left, q.left] ![(m : ℤ) ^ 2 * (j : ℤ), -(j : ℤ)]).Gen, c.IsGen :=
      (congrArg (fun d => ∃ c : (LB.LinComb L ![𝟙 A.left, q.left] d).Gen, c.IsGen) hpow).mp ⟨β, hβ⟩
    obtain ⟨z, hz⟩ := hz
    exact exists_iso_of_power_difference_gen hL _ _ _ _ z hz
  obtain ⟨z, hz⟩ := hiso
  let Q : ChartPull B M q.left := by
    have hq : (fun _ : PUnit => q.left ≫ 𝟙 A.left) = fun _ => q.left := funext fun _ => Category.comp_id _
    exact (congrArg (fun g => ChartPull (LB.LinComb L g (fun _ => (j : ℤ))) M q.left) hq).mp
      (ChartPull.linComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (j : ℤ)) q.left)
  obtain ⟨w, hw⟩ := (ChartPull.pull M q.left).iso_of_common Q hM
  have hv : Subsingleton (CohomologyOn (toMod P) ⊤ (n + 1)) := by
    change Subsingleton (CohomologyOn
      (toMod (LB.LinComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (m : ℤ) ^ 2 * (j : ℤ)))) ⊤ (n + 1))
    rw [hmt]
    exact hb t ht n
  obtain ⟨d, i, hi, hif⟩ := isProjOver_of_relAmple hL hAmp
  letI := hi
  let U (a : Fin (d + 1)) := i ⁻¹ᵁ PSpace.coordinateOpen K d a
  let V (a : Fin (d + 1)) := q.left ⁻¹ᵁ U a
  have hcov : ⨆ a, U a = ⊤ := i.iSup_preimage_eq_top (PSpace.iSup_coordinateOpen K d)
  have ha (s : Finset (Fin (d + 1))) (hs : s.Nonempty) : IsAffineOpen (coverInter ⊤ U s) :=
    (coverInter_pull (π := i) (PSpace.coordinateOpen K d) s).symm ▸
      (PSpace.isAffineOpen_coordinateInter K d hs).preimage i
  have ha' (s : Finset (Fin (d + 1))) (hs : s.Nonempty) : IsAffineOpen (coverInter ⊤ V s) :=
    (coverInter_pull (π := q.left) U s).symm ▸ (ha s hs).preimage q.left
  have hp : (cech A.hom (toMod P) V).ExactAt (n + 1) :=
    (exactAt_cech_iff_subsingleton_cohomology A.hom hP V
      (q.left.iSup_preimage_eq_top hcov).ge ha' _).mpr hv
  let D := cechIsoOfIsGen A.hom V (hM.pull q.left) hB hw ≪≫ cechIsoOfIsGen A.hom V hB hP hz
  have hp' := hp.of_iso D.symm
  exact (exactAt_cech_iff_subsingleton_cohomology A.hom hM U hcov.ge ha _).mp
    (exactAt_cech_of_pull_average A.hom (Over.w q) hτ hmul hD hcard.unit hcard.unit_spec M U _ hp')

end GlobalTheory.PrincipalSections
