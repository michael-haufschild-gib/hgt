import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PrincipalSectionsDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.AffineSectionCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.IntegralSectionProducts
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PowerSectionRankGrowth
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProjectiveTwistSectionGrowth
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TorsionSectionDecomposition
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.VeryAmplePowerComparison

/-! The positive powers of a symmetric principal polarization have
section dimension equal to the exponent raised to the relative dimension. -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj TopologicalSpace
open GlobalTheory.CommPairing GlobalTheory.LineBundleSections GlobalTheory.MulSplit
open GlobalTheory.ProjectiveSections GlobalTheory.SchemeCohomology UpperTheory.Cb
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K] [IsAlgClosed K] {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}

private theorem exists_power_section_growth [IsIntegral A.left] (hL : L.IsLB)
    (hAmp : RelAmple A L) (d : ℕ) [SmoothOfRelativeDimension d A.hom] :
    let h (n : ℕ) := Module.finrank Γ(Spec (.of K), ⊤) (Sg L A.hom (Finsupp.single (𝟙 A.left) (n : ℤ)))
    ∃ N b c C : ℕ, 1 ≤ N ∧ ∀ t : ℕ, b ≤ t → 1 ≤ t →
      t ^ d ≤ c * h (N * t) ∧ h (N * t) ≤ C * t ^ d := by
  let O : (Spec (.of K)).Opens := ⊤
  let V := A.hom ⁻¹ᵁ O
  let π := V.ι
  let Y := V.toScheme
  let f := π ≫ A.hom
  let q := A.hom ∣_ O
  letI : IsIso π := inferInstanceAs (IsIso A.left.topIso.hom)
  letI : IsIso O.ι := inferInstanceAs (IsIso (Spec (.of K)).topIso.hom)
  letI : IsIntegral Y := IsIntegral.of_isIso (inv π)
  letI : SmoothOfRelativeDimension d f := by
    have h : SmoothOfRelativeDimension (0 + d) (π ≫ A.hom) := inferInstance
    simpa only [Nat.zero_add] using h
  have hp := isProjOver_of_relAmple hL hAmp
  have hp' : IsProjOver f := hp.restrict_clopen V isClosed_univ
  letI : CompactSpace Y := hp'.compactSpace
  letI : Y.IsSeparated := hp'.isSeparated
  obtain ⟨N, hN, m, s, hc, hs⟩ := hAmp O (isAffineOpen_top _)
  let H := powOver A L O N
  have hH : H.IsLB := hL.linComb _ _
  choose r hr using fun i => (hs i).2
  have hf : q ≫ O.ι = f := morphismRestrict_ι _ _
  have hsurj (i : Fin (m + 1)) : letI := sectionAlgebra f (nonzeroLocus (s i))
      Function.Surjective (MvPolynomial.aeval (R := K) (r i)) := by
    have H := sectionAlgebra_comp_iso q O.ι _ (r i) (hr i).2
    rw [hf] at H
    exact H
  obtain ⟨b, c, C, -, hgr⟩ :=
    finrank_twistSections_growth f d hH s hc.ge (fun i => (hs i).1) r (fun i => (hr i).1) hsurj
  refine ⟨N, b, c, C, hN, fun t hb ht => ?_⟩
  let g : PUnit → (A.left ⟶ A.left) := fun _ => 𝟙 A.left
  let e : PUnit → ℤ := fun _ => ((N * t : ℕ) : ℤ)
  have hd : dv g e = Finsupp.single (𝟙 A.left) ((N * t : ℕ) : ℤ) := Fintype.sum_unique _
  have ht' := (finrank_formalSections A.hom g e hL hd).trans (finrank_trivialTwist_of_iso A.hom hp hL π N t)
  obtain ⟨hl, hu⟩ := hgr t hb ht
  exact ⟨(congrArg (fun x => t ^ d ≤ c * x) ht').mpr hl,
    (congrArg (fun x => x ≤ C * t ^ d) ht').mpr hu⟩

/-- Torsion splitting determines the ranks on multiples by invertible squares.
Multiplication by a nonzero first-power section makes ranks monotone, so the
growth of a very ample power determines the ranks at all positive exponents. -/
theorem finrank_sections_pow_eq_pow (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L)
    (hK : KTriv A L) (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : Spec (.of K), ∃ U : (Spec (.of K)).Opens, s ∈ U ∧
      ∃ t : (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (d : ℕ) [SmoothOfRelativeDimension d A.hom] (j : ℕ) (hj : 1 ≤ j) :
    Module.finrank Γ(Spec (.of K), ⊤) (Sg L A.hom (Finsupp.single (𝟙 A.left) (j : ℤ))) = j ^ d := by
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  letI : GeometricallyIntegral A.hom :=
    geometricallyIntegral_of_quasiCompact_of_smooth_of_geometricallyConnected A.hom
  letI : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let S := Γ(Spec (.of K), ⊤)
  let eK : S ≃+* K := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  letI : Field S := (MulEquiv.isField (Semifield.toIsField K) eK.toMulEquiv).toField
  let P (n : ℕ) := Sg L A.hom (Finsupp.single (𝟙 A.left) (n : ℤ))
  let h (n : ℕ) := Module.finrank S (P n)
  letI (n : ℕ) : Module.Finite S (P n) :=
    moduleFinite_formalSections A.hom (isProjOver_of_relAmple hL hAmp) hL _
  have h₁ : h 1 = 1 := finrank_sections_eq_one hA hL hAmp hK hrig hsym d
  obtain ⟨w, hw⟩ : ∃ w : P 1, w ≠ 0 := by
    by_contra! hz
    letI : Subsingleton (P 1) := ⟨fun u v => (hz u).trans (hz v).symm⟩
    have h₀ : h 1 = 0 := Module.finrank_zero_of_subsingleton
    omega
  have hmono : Monotone h := monotone_nat_of_le_succ fun n => by
    obtain ⟨mulBy, hmulBy⟩ := exists_injective_mul_section hL
      (D := Finsupp.single (𝟙 A.left) (n : ℤ)) (w := w) hw
    have he : Finsupp.single (𝟙 A.left) (1 : ℤ) + Finsupp.single (𝟙 A.left) (n : ℤ) =
        Finsupp.single (𝟙 A.left) ((n + 1 : ℕ) : ℤ) := by
      rw [← Finsupp.single_add, Nat.cast_succ, add_comm 1]
    change Module.finrank S (P n) ≤ Module.finrank S (P (n + 1))
    letI : Module.Finite S
        (Sg L A.hom (Finsupp.single (𝟙 A.left) (1 : ℤ) + Finsupp.single (𝟙 A.left) (n : ℤ))) :=
      moduleFinite_formalSections A.hom (isProjOver_of_relAmple hL hAmp) hL _
    exact (mulBy.finrank_le_finrank_of_injective hmulBy).trans (le_of_eq
      (congrArg (fun v => Module.finrank S (Sg L A.hom v)) he))
  let G (n : ℕ) := (n : K) ≠ 0
  have hG (n : ℕ) : G n ∨ G (n + 1) := by
    by_cases hn : (n : K) = 0
    · exact Or.inr (by simp [G, Nat.cast_add, hn])
    · exact Or.inl hn
  have hrel (n m : ℕ) (hn : G n) (hm : 1 ≤ m) : h (n ^ 2 * m) = h (n ^ 2) * h m := by
    let T := {x : 𝟙_ (Over (Spec (.of K))) ⟶ A // x ^ n = 1}
    letI : Finite T := finite_prime_to_char_torsion hA n hn
    letI : Fintype T := Fintype.ofFinite T
    have hsplit (v : ℕ) (hv : 1 ≤ v) : h (n ^ 2 * v) = Fintype.card T * h v := by
      obtain ⟨e⟩ := sections_mulPull_split hA hL hAmp hK hrig hsym n v hn (Nat.ne_zero_of_lt hv)
      have he : ((n ^ 2 * v : ℕ) : ℤ) = (n : ℤ) ^ 2 * (v : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_pow]
      change Module.finrank S (Sg L A.hom (Finsupp.single (𝟙 A.left) ((n ^ 2 * v : ℕ) : ℤ))) = _
      rw [he, e.finrank_eq]
      change Module.finrank S (T → P v) = Fintype.card T * Module.finrank S (P v)
      rw [Module.finrank_pi_fintype]
      exact Finset.sum_const_nat fun _ _ => rfl
    have hs : h (n ^ 2) = Fintype.card T := by simpa only [Nat.mul_one, h₁] using hsplit 1 le_rfl
    simpa only [hs] using hsplit m hm
  obtain ⟨N, b, c, C, hN, hgr⟩ := exists_power_section_growth hL hAmp d
  exact FinrankGrowthBounds.eq_pow_of_growth h d G hG (by simp [G]) h₁ hmono hrel N b c C hN hgr j hj

end GlobalTheory.PrincipalSections
