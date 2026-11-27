import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleCoordinates
import GaloisForLFunctions.RHTower.Artin.IdealsArePrincipalUpToADescentSetOfPrimes

/-! The finite valuations of an idele define a fractional ideal.
This homomorphism is surjective and sends diagonal ideles to principal ideals. -/

noncomputable section

namespace GlobalTheory.Reciprocity

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped nonZeroDivisors
open GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]

theorem fractionalIdealUnits_eq_iff {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    I = J ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) = count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
  refine ⟨fun h v ↦ h ▸ rfl, fun h ↦ Units.ext ?_⟩
  rw [← finprod_heightOneSpectrum_factorization' (K := K) I.ne_zero,
    ← finprod_heightOneSpectrum_factorization' (K := K) J.ne_zero]
  exact finprod_congr fun v ↦ by rw [h v]

theorem coe_finprod_primeIdealUnit_zpow (n : HeightOneSpectrum (𝓞 K) → ℤ)
    (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    ((∏ᶠ v, idealUnit v.ne_bot ^ n v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n v := by
  have hfin : (Function.mulSupport fun v ↦ idealUnit v.ne_bot ^ n v).Finite :=
    (Filter.eventually_cofinite.1 hn).subset fun v hv h ↦ hv (by simp only [h, zpow_zero])
  rw [← Units.coeHom_apply, map_finprod _ hfin]
  exact finprod_congr fun v ↦ by rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, coe_idealUnit]

theorem count_finprod_primeIdealUnit_zpow (n : HeightOneSpectrum (𝓞 K) → ℤ)
    (hn : ∀ᶠ v in Filter.cofinite, n v = 0) (v : HeightOneSpectrum (𝓞 K)) :
    count K v ((∏ᶠ w, idealUnit w.ne_bot ^ n w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = n v := by
  rw [coe_finprod_primeIdealUnit_zpow n hn, count_finprod K v n hn]

theorem finprod_primeIdealUnit_zpow_count (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∏ᶠ v, idealUnit v.ne_bot ^ count K v (I : FractionalIdeal (𝓞 K)⁰ K) = I := by
  rw [fractionalIdealUnits_eq_iff]
  intro v
  exact count_finprod_primeIdealUnit_zpow _ (FractionalIdeal.finite_factors _) v

open Classical in
theorem count_primeIdealUnit (v w : HeightOneSpectrum (𝓞 K)) :
    count K w ((idealUnit v.ne_bot : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      if w = v then 1 else 0 := by
  rw [coe_idealUnit]
  split_ifs with h
  · subst h
    exact count_self K w
  · exact count_maximal_coprime K w (Ne.symm h)

namespace IdeleGroup

def ord (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ℤ :=
  -log (Valued.v ((x : (AdeleRing (𝓞 K) K)).2 v))

theorem valued_ne_zero (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    Valued.v ((x : (AdeleRing (𝓞 K) K)).2 v) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 (finiteProj v x).ne_zero

theorem ord_mul (v : HeightOneSpectrum (𝓞 K)) (x y : IdeleGroup K) :
    ord v (x * y) = ord v x + ord v y := by
  have h : ((x * y : IdeleGroup K) : (AdeleRing (𝓞 K) K)).2 v = (x : (AdeleRing (𝓞 K) K)).2 v * (y : (AdeleRing (𝓞 K) K)).2 v := rfl
  rw [ord, ord, ord, h, map_mul, log_mul (valued_ne_zero v x) (valued_ne_zero v y), neg_add]

@[simp]
theorem ord_one (v : HeightOneSpectrum (𝓞 K)) : ord v (1 : IdeleGroup K) = 0 := by
  have h : ((1 : IdeleGroup K) : (AdeleRing (𝓞 K) K)).2 v = 1 := rfl
  rw [ord, h, map_one, log_one, neg_zero]

theorem ord_inv (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ord v x⁻¹ = -ord v x := by
  have h := ord_mul v x x⁻¹
  rw [mul_inv_cancel, ord_one] at h
  omega

theorem mem_adicCompletionIntegers_iff_ord_nonneg (v : HeightOneSpectrum (𝓞 K))
    (x : IdeleGroup K) :
    (x : (AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K ↔ 0 ≤ ord v x := by
  rw [mem_adicCompletionIntegers, ord, neg_nonneg, log_le_iff_le_exp (valued_ne_zero v x),
    exp_zero]

theorem ord_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    ord v x = 0 ↔ (x : (AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : IdeleGroup K) : (AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers_iff_ord_nonneg, mem_adicCompletionIntegers_iff_ord_nonneg,
    ord_inv]
  omega

theorem eventually_ord_eq_zero (x : IdeleGroup K) :
    ∀ᶠ v in Filter.cofinite, ord v x = 0 :=
  ((x : (AdeleRing (𝓞 K) K)).2.2.and ((x⁻¹ : IdeleGroup K) : (AdeleRing (𝓞 K) K)).2.2).mono fun v hv ↦
    (ord_eq_zero_iff v x).2 hv

theorem ord_finiteEmbedding_self (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ord v (finiteEmbedding v a) = -log (Valued.v (a : v.adicCompletion K)) := by
  rw [ord, ← coe_finiteProj, finiteProj_finiteEmbedding]

theorem ord_finiteEmbedding_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (a : (v.adicCompletion K)ˣ) : ord w (finiteEmbedding v a) = 0 := by
  rw [ord, ← coe_finiteProj, finiteProj_finiteEmbedding_of_ne h, Units.val_one, map_one, log_one,
    neg_zero]

theorem ord_diagonal (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ord v (diagonal K a) = -log (v.valuation K a) := by
  rw [ord, ← coe_finiteProj, coe_finiteProj_diagonal, valuedAdicCompletion_eq_valuation']

open Classical in

theorem exists_ord_eq_ite (v : HeightOneSpectrum (𝓞 K)) :
    ∃ x : IdeleGroup K, ∀ w, ord w x = if w = v then 1 else 0 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  refine ⟨finiteEmbedding v (Units.mk0 _ hne), fun w ↦ ?_⟩
  split_ifs with h
  · subst h
    rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp,
      neg_neg]
  · exact ord_finiteEmbedding_of_ne h _

theorem finite_mulSupport_primeIdealUnit_zpow_ord (x : IdeleGroup K) :
    (Function.mulSupport fun v ↦ idealUnit v.ne_bot ^ ord v x).Finite :=
  (Filter.eventually_cofinite.1 (eventually_ord_eq_zero x)).subset fun v hv h ↦
    hv (by simp only [h, zpow_zero])

def toFractionalIdeal : IdeleGroup K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun x := ∏ᶠ v, idealUnit v.ne_bot ^ ord v x
  map_one' := by simp only [ord_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [ord_mul, zpow_add]
    exact finprod_mul_distrib (finite_mulSupport_primeIdealUnit_zpow_ord x)
      (finite_mulSupport_primeIdealUnit_zpow_ord y)

@[simp]
theorem count_toFractionalIdeal (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    count K v ((toFractionalIdeal x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = ord v x :=
  count_finprod_primeIdealUnit_zpow _ (eventually_ord_eq_zero x) v

theorem toFractionalIdeal_eq_iff {x : IdeleGroup K} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    toFractionalIdeal x = I ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ord v x = count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [fractionalIdealUnits_eq_iff, count_toFractionalIdeal]

open Classical in

theorem primeIdealUnit_mem_range (v : HeightOneSpectrum (𝓞 K)) :
    idealUnit v.ne_bot ∈ (toFractionalIdeal (K := K)).range := by
  obtain ⟨x, hx⟩ := exists_ord_eq_ite v
  refine ⟨x, toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  rw [hx, count_primeIdealUnit]

theorem toFractionalIdeal_surjective : Function.Surjective (toFractionalIdeal (K := K)) := by
  intro I
  have h : I ∈ (toFractionalIdeal (K := K)).range := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    exact finprod_induction (· ∈ (toFractionalIdeal (K := K)).range) (one_mem _)
      (fun _ _ ↦ mul_mem) fun v ↦ zpow_mem (primeIdealUnit_mem_range v) _
  exact h

theorem toFractionalIdeal_diagonal (a : Kˣ) :
    toFractionalIdeal (diagonal K a) = toPrincipalIdeal (𝓞 K) K a := by
  rw [toFractionalIdeal_eq_iff]
  intro v
  rw [ord_diagonal, GaloisForLFunctions.count_toPrincipalIdeal,
    GaloisForLFunctions.valuation_eq_exp_neg_ordAt K v a, log_exp, neg_neg]

end IdeleGroup

end GlobalTheory.Reciprocity
