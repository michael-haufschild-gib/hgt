import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PolynomialCechPositiveFiniteness

/-! At degree zero, compatible Laurent coefficients come from the augmented term
unless the cover consists of a single coordinate. -/

noncomputable section

open CategoryTheory HTGeometry MvPolynomial
open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [CommRing R]
  [IsNoetherianRing R]

private abbrev C (n : ℤ) := polynomialGradedCech (ι := ι) R n
private abbrev D (n : ℤ) := polynomialCechDatum (ι := ι) R n

private def augCochain {n : ℤ} (x : (D (ι := ι) (R := R) n).obj ∅) :
    (D (ι := ι) (R := R) n).Cochain :=
  fun s => if h : s = ∅ then h.symm ▸ x else 0

private theorem augCochain_isBot {n : ℤ} (x : (D (ι := ι) (R := R) n).obj ∅) :
    (D n).IsBot (augCochain x) :=
  fun _ h => dif_neg (Finset.nonempty_iff_ne_empty.1 h)

private def augToCycles (n : ℤ) : (D (ι := ι) (R := R) n).obj ∅ →ₗ[R]
    LinearMap.ker ((C (ι := ι) (R := R) n).d 0 1).hom where
  toFun x := ⟨⟨(D n).d (augCochain x), (D n).d_isDeg_of_isBot (augCochain_isBot x)⟩, by
    apply LinearMap.mem_ker.2
    apply Subtype.ext
    rw [polynomialGradedCech_d_val]
    exact (D n).d_d (augCochain x)⟩
  map_add' x y := by
    have h : augCochain (x + y) = augCochain x + augCochain y := by
      funext s
      by_cases e : s = ∅
      · subst s; simp [augCochain]
      · simp [augCochain, e]
    exact Subtype.ext (Subtype.ext (by rw [h, FinsetCechDatum.d_add]))
  map_smul' r x := by
    have h : augCochain (r • x) = r • augCochain x := by
      funext s
      by_cases e : s = ∅
      · subst s; simp [augCochain]
      · simp [augCochain, e]
    refine Subtype.ext (Subtype.ext ?_)
    change (D n).d (augCochain (r • x)) = r • (D n).d (augCochain x)
    rw [h]
    funext s
    simp only [FinsetCechDatum.d, Pi.smul_apply, Finset.smul_sum, homLocDatum_res_smul]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ r _

private theorem finite_polynomial_zero_cycles [Nonempty ι] (n : ℤ) :
    Module.Finite R (LinearMap.ker ((C (ι := ι) (R := R) n).d 0 1).hom) := by
  classical
  by_cases hcard : Fintype.card ι = 1
  · haveI : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.1 hcard.le
    have hs (s : Finset ι) : (localizedExponents s n).Finite := by
      apply Set.Subsingleton.finite
      intro a ha b hb
      funext i
      have one_term (z : ι → ℤ) : ∑ j, z j = z i :=
        Finset.sum_eq_single i (fun _ _ h => absurd (Subsingleton.elim _ _) h)
          (fun h => absurd (Finset.mem_univ i) h)
      exact (one_term a).symm.trans (ha.1.trans (hb.1.symm.trans (one_term b)))
    haveI (s : {s : Finset ι // s.card = 1}) : Module.Finite R ((D n).obj s.1) :=
      finite_homLoc_of_finite_exponents (hs s.1)
    haveI : Module.Finite R ((C n).X 0) :=
      Module.Finite.equiv ((D n).degreeLinearEquiv (R := R) 0).symm
    infer_instance
  · haveI : Module.Finite R ((D (ι := ι) (R := R) n).obj ∅) :=
      finite_homLoc_of_finite_exponents (finite_localizedExponents_empty (ι := ι) n)
    apply Module.Finite.of_surjective (augToCycles (ι := ι) (R := R) n)
    intro x
    have hdx : (D n).d x.1.1 = 0 := by
      rw [← polynomialGradedCech_d_val n 0 x.1]
      exact congrArg Subtype.val (LinearMap.mem_ker.1 x.2)
    have hc : x.1.1 Finset.univ = 0 := x.1.2 _ (by simpa only [Finset.card_univ, zero_add] using hcard)
    obtain ⟨b, hb, hdb⟩ := polynomialCech_exists_primitive x.1.2 hdx (fun a _ => by
      change localizedCoefficients R Finset.univ n (x.1.1 Finset.univ) a = 0
      rw [hc, map_zero, Finsupp.zero_apply])
    have e : augCochain (b ∅) = b := by
      funext s
      by_cases h : s = ∅
      · subst s; simp [augCochain]
      · rw [augCochain, dif_neg h, hb s (by simpa [Finset.card_eq_zero] using h)]
    exact ⟨b ∅, Subtype.ext (Subtype.ext (by change (D n).d (augCochain (b ∅)) = _;
      rw [e, hdb]))⟩

theorem finite_polynomialGradedCech_homology [Nonempty ι] (n : ℤ) (p : ℕ) :
    Module.Finite R ((C (ι := ι) (R := R) n).homology p) := by
  cases p with
  | succ p => exact finite_polynomialGradedCech_homology_succ n p
  | zero =>
    let S := (C (ι := ι) (R := R) n).sc' 0 0 1
    haveI : Module.Finite R (LinearMap.ker S.g.hom) := finite_polynomial_zero_cycles n
    haveI : Module.Finite R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) := inferInstance
    let e := (C n).homologyIsoSc' 0 0 1 (by simp) (by simp) ≪≫ S.moduleCatHomologyIso
    exact Module.Finite.equiv e.symm.toLinearEquiv

end GlobalTheory
