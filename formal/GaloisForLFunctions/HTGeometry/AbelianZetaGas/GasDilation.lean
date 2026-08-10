import GaloisForLFunctions.HTGeometry.AbelianZetaGas.KMSState
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DepthDilation

/-!
# The renormalisation embedding of the gas algebra

An injective map of modes transports monomials, and because the monomial product is computed mode by
mode the transport is a monoid homomorphism.  On the gas algebra it becomes a unital embedding which
intertwines the imaginary-time flows and pulls the Gibbs functional of the target back to the Gibbs
functional of the reindexed weights.  Applied to the depth dilation `δ_d : (p,j) ↦ (p,dj)` this is
the operator-algebraic clause of the renormalisation semigroup: `ι_d` intertwines `α` with `α∘d`,
and pulls `φ_σ` back to `φ_{dσ}`.
-/

namespace GaloisForLFunctions.HTGeometry

open GasWord

variable {M N : Type*}

/-! ## Transporting monomials along an injective map of modes -/

theorem mapDomain_tsub {f : M → N} (hf : Function.Injective f) (a b : M →₀ ℕ) :
    Finsupp.mapDomain f (a - b) = Finsupp.mapDomain f a - Finsupp.mapDomain f b := by
  refine Finsupp.ext fun n => ?_
  by_cases hn : n ∈ Set.range f
  · obtain ⟨m, rfl⟩ := hn
    rw [Finsupp.mapDomain_apply hf, Finsupp.tsub_apply, Finsupp.tsub_apply,
      Finsupp.mapDomain_apply hf, Finsupp.mapDomain_apply hf]
  · rw [Finsupp.mapDomain_notin_range _ n hn, Finsupp.tsub_apply,
      Finsupp.mapDomain_notin_range _ n hn, Finsupp.mapDomain_notin_range _ n hn]
    simp

/-- **Transport of monomials along an injective map of modes.** -/
noncomputable def wordMap (f : M → N) (hf : Function.Injective f) : GasWord M →* GasWord N where
  toFun x := ⟨Finsupp.mapDomain f x.raise, Finsupp.mapDomain f x.lower⟩
  map_one' := by
    refine GasWord.ext ?_ ?_ <;> simp
  map_mul' x y := by
    refine GasWord.ext ?_ ?_
    · show Finsupp.mapDomain f (x.raise + (y.raise - x.lower))
        = Finsupp.mapDomain f x.raise + (Finsupp.mapDomain f y.raise - Finsupp.mapDomain f x.lower)
      rw [Finsupp.mapDomain_add, mapDomain_tsub hf]
    · show Finsupp.mapDomain f (y.lower + (x.lower - y.raise))
        = Finsupp.mapDomain f y.lower + (Finsupp.mapDomain f x.lower - Finsupp.mapDomain f y.raise)
      rw [Finsupp.mapDomain_add, mapDomain_tsub hf]

@[simp] theorem wordMap_raise (f : M → N) (hf : Function.Injective f) (x : GasWord M) :
    (wordMap f hf x).raise = Finsupp.mapDomain f x.raise := rfl

@[simp] theorem wordMap_lower (f : M → N) (hf : Function.Injective f) (x : GasWord M) :
    (wordMap f hf x).lower = Finsupp.mapDomain f x.lower := rfl

theorem charge_wordMap (f : M → N) (hf : Function.Injective f) (x : GasWord M) :
    charge (wordMap f hf x) = Finsupp.mapDomain f (charge x) := by
  refine Finsupp.ext fun n => ?_
  by_cases hn : n ∈ Set.range f
  · obtain ⟨m, rfl⟩ := hn
    rw [charge_apply, Finsupp.mapDomain_apply hf, charge_apply, wordMap_raise, wordMap_lower,
      Finsupp.mapDomain_apply hf, Finsupp.mapDomain_apply hf]
  · rw [charge_apply, Finsupp.mapDomain_notin_range _ n hn, wordMap_raise, wordMap_lower,
      Finsupp.mapDomain_notin_range _ n hn, Finsupp.mapDomain_notin_range _ n hn]
    simp

theorem natToInt_mapDomain (f : M → N) (hf : Function.Injective f) (a : M →₀ ℕ) :
    natToInt (Finsupp.mapDomain f a) = Finsupp.mapDomain f (natToInt a) := by
  refine Finsupp.ext fun n => ?_
  by_cases hn : n ∈ Set.range f
  · obtain ⟨m, rfl⟩ := hn
    rw [natToInt_apply, Finsupp.mapDomain_apply hf, Finsupp.mapDomain_apply hf, natToInt_apply]
  · rw [natToInt_apply, Finsupp.mapDomain_notin_range _ n hn,
      Finsupp.mapDomain_notin_range _ n hn]
    simp

theorem zprod_mapDomain (q : N → ℂ) {f : M → N} (hf : Function.Injective f) (g : M →₀ ℤ) :
    zprod q (Finsupp.mapDomain f g) = zprod (fun m => q (f m)) g := by
  rw [zprod, zprod, Finsupp.prod_mapDomain_index_inj hf]

/-! ## The reindexed weights -/

theorem chi_wordMap (q : N → ℂ) {f : M → N} (hf : Function.Injective f) (x : GasWord M) :
    chi q (wordMap f hf x) = chi (fun m => q (f m)) x := by
  rw [chi, chi, charge_wordMap, zprod_mapDomain q hf]

theorem gibbsWeight_wordMap (q : N → ℂ) {f : M → N} (hf : Function.Injective f) (x : GasWord M) :
    gibbsWeight q (wordMap f hf x) = gibbsWeight (fun m => q (f m)) x := by
  classical
  by_cases hdiag : x.raise = x.lower
  · have hd : (wordMap f hf x).raise = (wordMap f hf x).lower := by
      rw [wordMap_raise, wordMap_lower, hdiag]
    rw [gibbsWeight_of_diag hd, gibbsWeight_of_diag hdiag, wordMap_raise,
      natToInt_mapDomain f hf, zprod_mapDomain q hf]
  · have hd : ¬ (wordMap f hf x).raise = (wordMap f hf x).lower := by
      rw [wordMap_raise, wordMap_lower]
      exact fun h => hdiag (Finsupp.mapDomain_injective hf h)
    rw [gibbsWeight_of_not_diag hd, gibbsWeight_of_not_diag hdiag]

/-! ## The embedding of algebras -/

/-- **The unital embedding of gas algebras induced by an injective map of modes.** -/
noncomputable def gasEmbed (f : M → N) (hf : Function.Injective f) :
    GasAlgebra M →ₐ[ℂ] GasAlgebra N :=
  MonoidAlgebra.lift ℂ (GasAlgebra N) (GasWord M)
    ((MonoidAlgebra.of ℂ (GasWord N)).comp (wordMap f hf))

theorem gasEmbed_single (f : M → N) (hf : Function.Injective f) (x : GasWord M) (c : ℂ) :
    gasEmbed f hf (MonoidAlgebra.single x c)
      = MonoidAlgebra.single (wordMap f hf x) c := by
  rw [gasEmbed, MonoidAlgebra.lift_single]
  show c • MonoidAlgebra.single (wordMap f hf x) (1 : ℂ) = _
  rw [MonoidAlgebra.smul_single', mul_one]

/-- **The embedding intertwines the two imaginary-time flows.** -/
theorem gasEmbed_twist (q : N → ℂ) (hq : ∀ n, q n ≠ 0) {f : M → N}
    (hf : Function.Injective f) (a : GasAlgebra M) :
    gasEmbed f hf (twist (fun m => q (f m)) (fun m => hq (f m)) a)
      = twist q hq (gasEmbed f hf a) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]
  | single x c =>
    rw [twist_single, gasEmbed_single, gasEmbed_single, twist_single, chi_wordMap]

/-- **The embedding pulls the Gibbs functional back to the reindexed one.** -/
theorem gibbs_comp_gasEmbed (q : N → ℂ) {f : M → N} (hf : Function.Injective f)
    (a : GasAlgebra M) :
    gibbs q (gasEmbed f hf a) = gibbs (fun m => q (f m)) a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  | single x c =>
    rw [gasEmbed_single, gibbs_single, gibbs_single, gibbsWeight_wordMap]

/-! ## The depth dilation -/

/-- **The renormalisation embedding `ι_d`.** -/
noncomputable def gasDilate {d : ℕ} (hd : 1 ≤ d) :
    GasAlgebra AbelianZetaMode →ₐ[ℂ] GasAlgebra AbelianZetaMode :=
  gasEmbed (depthDilation d) (depthDilation_injective hd)

theorem gasNome_comp_depthDilation (θ : AbelianZetaParameters) {d : ℕ} (hd : 1 ≤ d)
    (m : AbelianZetaMode) :
    gasNome θ (depthDilation d m) = gasNome (θ.depthDilate d hd) m := by
  rw [gasNome, gasNome, AbelianZetaParameters.ratio_depthDilation θ hd]

/-- **(GAS.11), operator clause.**  The renormalisation embedding intertwines the imaginary-time
flow at temperature `σ` with the flow at temperature `dσ`. -/
theorem gasDilate_twist (θ : AbelianZetaParameters) {d : ℕ} (hd : 1 ≤ d)
    (a : GasAlgebra AbelianZetaMode) :
    gasDilate hd (gasTwist (θ.depthDilate d hd) a) = gasTwist θ (gasDilate hd a) := by
  have hfun : (fun m => gasNome θ (depthDilation d m)) = gasNome (θ.depthDilate d hd) :=
    funext fun m => gasNome_comp_depthDilation θ hd m
  have h := gasEmbed_twist (gasNome θ) (gasNome_ne_zero θ) (depthDilation_injective hd) a
  rw [gasDilate, gasTwist, gasTwist, twist]
  rw [twist] at h
  simp only [hfun] at h
  exact h

/-- **(GAS.11), state clause.**  Pulling the equilibrium functional back along the renormalisation
embedding is the same as raising the temperature by the factor `d`. -/
theorem gasGibbs_comp_gasDilate (θ : AbelianZetaParameters) {d : ℕ} (hd : 1 ≤ d)
    (a : GasAlgebra AbelianZetaMode) :
    gasGibbs θ (gasDilate hd a) = gasGibbs (θ.depthDilate d hd) a := by
  have hfun : (fun m => gasNome θ (depthDilation d m)) = gasNome (θ.depthDilate d hd) :=
    funext fun m => gasNome_comp_depthDilation θ hd m
  have h := gibbs_comp_gasEmbed (gasNome θ) (depthDilation_injective hd) a
  rw [gasDilate, gasGibbs, gasGibbs]
  rw [hfun] at h
  exact h

/-- Transport is functorial in the mode map. -/
theorem wordMap_comp {P : Type*} {f : M → N} (hf : Function.Injective f)
    {g : N → P} (hg : Function.Injective g) {h : M → P} (hh : Function.Injective h)
    (hcomp : ∀ m, g (f m) = h m) (x : GasWord M) :
    wordMap g hg (wordMap f hf x) = wordMap h hh x := by
  have hfun : g ∘ f = h := funext hcomp
  refine GasWord.ext ?_ ?_
  · show Finsupp.mapDomain g (Finsupp.mapDomain f x.raise) = Finsupp.mapDomain h x.raise
    rw [← Finsupp.mapDomain_comp, hfun]
  · show Finsupp.mapDomain g (Finsupp.mapDomain f x.lower) = Finsupp.mapDomain h x.lower
    rw [← Finsupp.mapDomain_comp, hfun]

theorem gasEmbed_comp {P : Type*} {f : M → N} (hf : Function.Injective f)
    {g : N → P} (hg : Function.Injective g) {h : M → P} (hh : Function.Injective h)
    (hcomp : ∀ m, g (f m) = h m) (a : GasAlgebra M) :
    gasEmbed g hg (gasEmbed f hf a) = gasEmbed h hh a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
  | single x c =>
    rw [gasEmbed_single, gasEmbed_single, gasEmbed_single, wordMap_comp hf hg hh hcomp]

/-- **(GAS.11), semigroup clause.**  The renormalisation embeddings compose as the multiplicative
monoid of depths: `ι_d ∘ ι_e = ι_{de}`. -/
theorem gasDilate_comp {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (hde : 1 ≤ d * e)
    (a : GasAlgebra AbelianZetaMode) :
    gasDilate hd (gasDilate he a) = gasDilate hde a :=
  gasEmbed_comp (depthDilation_injective he) (depthDilation_injective hd)
    (depthDilation_injective hde) (depthDilation_comp hd he) a

end GaloisForLFunctions.HTGeometry
