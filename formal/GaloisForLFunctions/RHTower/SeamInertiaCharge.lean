/-
# Inertia = Charge: the seam Krein index of the FE conjugate-pair carrier is the deck ladder charge

The functional equation forces, on the completed section, an indefinite Krein/Weil Gram whose negative
index `κ₋` counts the off-line zeros.  Two exact counts of that same off-line data have been isolated
separately: the **Krein negative index** (`exact_neg_inertia`, an analytic signature) and the additive
**deck ladder charge** `wCharge (2^m)` (`DeckChargeCalculus`, a `2`-adic monodromy invariant).  This
file welds them on one object.

The genuine content is that the Krein exact-inertia count is made **unconditional** for the concrete
FE conjugate-pair carrier.  `exact_neg_inertia` (and `factoredKrein_kreinNonneg_iff`) discharge the
inertia against a surjectivity hypothesis `hT` — the "sole remaining arithmetic input" flagged in
`KreinLangerInertia`.  Here that hypothesis is proved outright: choosing `2k` off-pole nodes in the
upper half-plane, the `2k` Cauchy vectors of the poles `{t_i}∪{t̄_i}` are linearly independent
(`cauchy_linearIndependent`), the derived carrier vectors `w_i = e_i+a_i`, `u_i = e_i−a_i` are
independent by an invertible pairing, and the stacked evaluation is surjective
(`eval_surjective_rect`).  Consequences, all unconditional:

* `seamCarrier_exact_inertia` — the FE seam Gram has negative index **exactly `k`** (= the number of
  off-line zeros): every negative-definite subspace has `dim ≤ k`, and one of `dim = k` exists.
* `seamCarrier_kreinNonneg_iff` — the seam Gram is definite (`KreinNonneg`, a positive polarization)
  iff `k = 0`.
* `seam_inertia_eq_charge` — **the weld**: the seam Gram is definite iff the deck ladder charge of the
  configuration vanishes at every rung, `∀ m, wCharge (2^m) (k : ℤ) = 0`.  The analytic definiteness
  face and the `2`-adic charge face are one condition; `k = 0` is their common value.

Nothing is propagated by a flow: `k` off-line points fix an indefinite form, and definiteness is a
constraint on that form, read equally as an index (Krein) or as a `2`-adic charge (deck).
-/
import GaloisForLFunctions.RHTower.SeamSpectralFlow
import GaloisForLFunctions.RHTower.DeckChargeLadder

open Complex Matrix GaloisForLFunctions
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ### The FE conjugate-pair carrier vectors -/

/-- The `+` carrier vector of the FE conjugate pair at pole `t_i` on nodes `z`:
`w_i = e_i + a_i` with `a_i = 1/(t_i-z)`, `e_i = 1/(t̄_i-z)`. -/
def seamW {k N : ℕ} (t : Fin k → ℂ) (z : Fin N → ℂ) : Fin k → (Fin N → ℂ) :=
  fun i j => (star (t i) - z j)⁻¹ + (t i - z j)⁻¹

/-- The `−` carrier vector of the FE conjugate pair: `u_i = e_i − a_i`. -/
def seamU {k N : ℕ} (t : Fin k → ℂ) (z : Fin N → ℂ) : Fin k → (Fin N → ℂ) :=
  fun i j => (star (t i) - z j)⁻¹ - (t i - z j)⁻¹

/-! ### Two reusable linear-algebra primitives -/

/-- **Node existence.**  For any finite index `ι'`, there is an injective family of `ι'`-many points
of the open upper half-plane avoiding the finite pole set `{t_i}∪{t̄_i}`: the upper half-plane is
infinite and we remove finitely many points. -/
theorem exists_offpole_nodes {ι' : Type*} [Fintype ι'] {k : ℕ} (t : Fin k → ℂ) :
    ∃ z : ι' → ℂ, Function.Injective z ∧ (∀ j, 0 < (z j).im)
      ∧ (∀ (i : Fin k) (j : ι'), z j ≠ t i) ∧ (∀ (i : Fin k) (j : ι'), z j ≠ star (t i)) := by
  classical
  have hforb : (Set.range t ∪ Set.range (fun i => star (t i))).Finite :=
    (Set.finite_range t).union (Set.finite_range _)
  have hUHP : {w : ℂ | 0 < w.im}.Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => Complex.I * (m + 1))
    · intro a b h
      simp only [mul_right_inj' Complex.I_ne_zero] at h
      have : (a : ℂ) = b := by linear_combination h
      exact_mod_cast this
    · intro m
      simp only [Set.mem_setOf_eq, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.add_re, Complex.one_re, Complex.natCast_re, zero_mul, one_mul, zero_add]
      positivity
  have hInf : ({w : ℂ | 0 < w.im} \
      (Set.range t ∪ Set.range (fun i => star (t i)))).Infinite := hUHP.diff hforb
  haveI : Infinite ({w : ℂ | 0 < w.im} \
      (Set.range t ∪ Set.range (fun i => star (t i))) : Set ℂ) := hInf.to_subtype
  set emb : ι' ↪ ({w : ℂ | 0 < w.im} \
      (Set.range t ∪ Set.range (fun i => star (t i))) : Set ℂ) :=
    (Fintype.equivFin ι').toEmbedding.trans
      ((Fin.valEmbedding).trans (Infinite.natEmbedding _)) with hemb
  refine ⟨fun j => (emb j : ℂ), ?_, ?_, ?_, ?_⟩
  · intro a b h; exact emb.injective (Subtype.ext h)
  · intro j; exact (emb j).2.1
  · intro i j hj
    exact (emb j).2.2 (Set.mem_union_left _ ⟨i, hj.symm⟩)
  · intro i j hj
    exact (emb j).2.2 (Set.mem_union_right _ ⟨i, hj.symm⟩)

/-- **Pairing transfer.**  If a family `C` indexed by `Fin k ⊕ Fin k` is linearly independent, so is
the family `w_i = C(inr i)+C(inl i)`, `u_i = C(inr i)−C(inl i)` (the invertible `[[1,1],[1,−1]]`
pairing on each `{inl i, inr i}` block). -/
theorem linearIndependent_pm_of {N k : ℕ} (C : (Fin k ⊕ Fin k) → (Fin N → ℂ))
    (hC : LinearIndependent ℂ C) :
    LinearIndependent ℂ (fun j : Fin k ⊕ Fin k =>
      match j with
      | Sum.inl i => C (Sum.inr i) + C (Sum.inl i)
      | Sum.inr i => C (Sum.inr i) - C (Sum.inl i)) := by
  rw [Fintype.linearIndependent_iff]
  intro d hd
  have hCindep := (Fintype.linearIndependent_iff).mp hC
  set coef : (Fin k ⊕ Fin k) → ℂ := fun j =>
    match j with
    | Sum.inl i => d (Sum.inl i) - d (Sum.inr i)
    | Sum.inr i => d (Sum.inl i) + d (Sum.inr i) with hcoef
  have key : ∑ j, coef j • C j = ∑ j, d j •
      (match j with
        | Sum.inl i => C (Sum.inr i) + C (Sum.inl i)
        | Sum.inr i => C (Sum.inr i) - C (Sum.inl i)) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [hcoef, smul_add, smul_sub, sub_smul, add_smul]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by module)
  rw [hd] at key
  have hz := hCindep coef key
  intro j
  cases j with
  | inl i =>
    have h1 := hz (Sum.inl i); have h2 := hz (Sum.inr i)
    simp only [hcoef] at h1 h2; linear_combination (h1 + h2) / 2
  | inr i =>
    have h1 := hz (Sum.inl i); have h2 := hz (Sum.inr i)
    simp only [hcoef] at h1 h2; linear_combination (h2 - h1) / 2

/-! ### The unconditional surjectivity discharge -/

/-- **The carrier evaluation is surjective (unconditional).**  For `k` distinct off-line poles
`t_i ∈ ℂ⁺`, there is a node configuration `z` on `Fin (2k)` (in `ℂ⁺`, off the poles) for which the
stacked evaluation `(Φ,Ψ) : x ↦ (⟨w_i,x⟩, ⟨u_i,x⟩)` against the FE carrier vectors is surjective — the
Cauchy non-degeneracy that `exact_neg_inertia` / `factoredKrein_kreinNonneg_iff` take as a hypothesis,
here proved.  The `Φ, Ψ` are the honest evaluation maps (`hΦ`, `hΨ`). -/
theorem exists_seamCarrier_surjective {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) :
    ∃ (z : Fin (2 * k) → ℂ) (Φ Ψ : (Fin (2 * k) → ℂ) →ₗ[ℂ] (Fin k → ℂ)),
      (∀ (y : Fin (2 * k) → ℂ) (i : Fin k), Φ y i = star (seamW t z i) ⬝ᵥ y)
      ∧ (∀ (y : Fin (2 * k) → ℂ) (i : Fin k), Ψ y i = star (seamU t z i) ⬝ᵥ y)
      ∧ Function.Surjective (Φ.prod Ψ) := by
  classical
  -- poles indexed by `Fin k ⊕ Fin k`
  set P : (Fin k ⊕ Fin k) → ℂ := Sum.elim t (fun i => star (t i)) with hP
  have hPinj : Function.Injective P := by
    rintro (i | i) (j | j) h <;>
      simp only [hP, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (htinj h)
    · exfalso
      have h1 := ht i; rw [h] at h1
      simp only [Complex.star_def, Complex.conj_im] at h1; linarith [ht j]
    · exfalso
      have h1 := ht j; rw [← h] at h1
      simp only [Complex.star_def, Complex.conj_im] at h1; linarith [ht i]
    · refine congrArg Sum.inr (htinj ?_)
      have := congrArg star h; rwa [star_star, star_star] at this
  -- off-pole nodes indexed by `Fin k ⊕ Fin k`
  obtain ⟨zc, hzcinj, hzcim, hzct, hzcst⟩ :=
    exists_offpole_nodes (ι' := Fin k ⊕ Fin k) t
  have hPz : ∀ i j, P i ≠ zc j := by
    rintro (i | i) j <;> simp only [hP, Sum.elim_inl, Sum.elim_inr]
    · exact fun h => hzct i j h.symm
    · exact fun h => hzcst i j h.symm
  -- square Cauchy family (independent)
  have hCsq : LinearIndependent ℂ (fun i => (fun l => (P i - zc l)⁻¹ : (Fin k ⊕ Fin k) → ℂ)) :=
    cauchy_linearIndependent P zc hPinj hzcinj hPz
  -- transport the coordinate index `Fin k ⊕ Fin k ≃ Fin (2k)`
  set e : Fin (2 * k) ≃ (Fin k ⊕ Fin k) :=
    (Fintype.equivFinOfCardEq (by simp [two_mul])).symm with he
  set z : Fin (2 * k) → ℂ := fun m => zc (e m) with hz
  set C : (Fin k ⊕ Fin k) → (Fin (2 * k) → ℂ) := fun i m => (P i - z m)⁻¹ with hC
  have hCindep : LinearIndependent ℂ C := by
    have h2 := hCsq.map' (LinearEquiv.funCongrLeft ℂ ℂ e).toLinearMap
      (LinearEquiv.funCongrLeft ℂ ℂ e).ker
    have heq : (⇑(LinearEquiv.funCongrLeft ℂ ℂ e).toLinearMap ∘
        (fun i => (fun l => (P i - zc l)⁻¹ : (Fin k ⊕ Fin k) → ℂ))) = C := by
      ext i m; rfl
    rw [heq] at h2; exact h2
  -- carrier vectors
  have hWC : seamW t z = fun i => C (Sum.inr i) + C (Sum.inl i) := by
    funext i j; simp only [seamW, hC, hP, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
  have hUC : seamU t z = fun i => C (Sum.inr i) - C (Sum.inl i) := by
    funext i j; simp only [seamU, hC, hP, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
  -- the combined family `V = Sum.elim w u` is independent
  set V : (Fin k ⊕ Fin k) → (Fin (2 * k) → ℂ) :=
    Sum.elim (seamW t z) (seamU t z) with hV
  have hVeq : V = (fun j : Fin k ⊕ Fin k =>
      match j with
      | Sum.inl i => C (Sum.inr i) + C (Sum.inl i)
      | Sum.inr i => C (Sum.inr i) - C (Sum.inl i)) := by
    funext j; cases j with
    | inl i => rw [hV, Sum.elim_inl, hWC]
    | inr i => rw [hV, Sum.elim_inr, hUC]
  have hVindep : LinearIndependent ℂ V := by
    rw [hVeq]; exact linearIndependent_pm_of C hCindep
  -- stacked evaluation surjective
  have hevalV : Function.Surjective
      (fun x : Fin (2 * k) → ℂ => (fun j => star (V j) ⬝ᵥ x : (Fin k ⊕ Fin k) → ℂ)) :=
    eval_surjective_rect V hVindep
  -- build Φ, Ψ
  set Φ : (Fin (2 * k) → ℂ) →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun x => star (seamW t z i) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ x y
      map_smul' := fun c x => dotProduct_smul c _ x }) with hΦdef
  set Ψ : (Fin (2 * k) → ℂ) →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i =>
    { toFun := fun x => star (seamU t z i) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ x y
      map_smul' := fun c x => dotProduct_smul c _ x }) with hΨdef
  refine ⟨z, Φ, Ψ, fun y i => rfl, fun y i => rfl, ?_⟩
  -- surjectivity of the product, via the sum-arrow equiv
  have hcompose : ⇑(Φ.prod Ψ) = ⇑(Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) ℂ) ∘
      (fun x : Fin (2 * k) → ℂ => (fun j => star (V j) ⬝ᵥ x : (Fin k ⊕ Fin k) → ℂ)) := by
    funext x
    refine Prod.ext ?_ ?_ <;> funext i <;> rfl
  rw [hcompose]
  exact (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) ℂ).surjective.comp hevalV

/-! ### The exact inertia and the definiteness face, unconditionally -/

/-- **Exact seam Krein index `κ₋ = k`, unconditional.**  For `k` distinct off-line poles `t_i ∈ ℂ⁺`,
there is a node configuration for which the FE seam Gram `factoredKreinForm (seamW) (seamU)` has
negative index exactly `k`: every negative-definite subspace has `dim ≤ k`, and one of `dim = k`
exists.  This is `exact_neg_inertia` with its surjectivity hypothesis discharged. -/
theorem seamCarrier_exact_inertia {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) :
    ∃ z : Fin (2 * k) → ℂ,
      (∀ W : Submodule ℂ (Fin (2 * k) → ℂ),
          (∀ y ∈ W, y ≠ 0 →
            (star y ⬝ᵥ (factoredKreinForm (seamW t z) (seamU t z)).mulVec y).re < 0)
          → Module.finrank ℂ W ≤ k)
      ∧ (∃ W : Submodule ℂ (Fin (2 * k) → ℂ), Module.finrank ℂ W = k ∧
          ∀ y ∈ W, y ≠ 0 →
            (star y ⬝ᵥ (factoredKreinForm (seamW t z) (seamU t z)).mulVec y).re < 0) := by
  obtain ⟨z, Φ, Ψ, hΦ, hΨ, hT⟩ := exists_seamCarrier_surjective t ht htinj
  exact ⟨z, exact_neg_inertia (seamW t z) (seamU t z) Φ Ψ hΦ hΨ hT⟩

/-- **Definiteness ⟺ no off-line zero, unconditional.**  The FE seam Gram is definite (`KreinNonneg`,
a positive polarization) iff `k = 0`.  This is `factoredKrein_kreinNonneg_iff` with its surjectivity
hypothesis discharged. -/
theorem seamCarrier_kreinNonneg_iff {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) :
    ∃ z : Fin (2 * k) → ℂ, KreinNonneg (factoredKreinForm (seamW t z) (seamU t z)) ↔ k = 0 := by
  obtain ⟨z, Φ, Ψ, hΦ, hΨ, hT⟩ := exists_seamCarrier_surjective t ht htinj
  exact ⟨z, factoredKrein_kreinNonneg_iff (seamW t z) (seamU t z) Φ Ψ hΦ hΨ hT⟩

/-- `k = 0 ⟺ every rung of the deck ladder charge vanishes`.  The total off-line multiplicity `k`
is zero iff `wCharge (2^m) (k : ℤ) = 0` for all `m`: a nonzero `k` is not divisible by `2^m` once
`2^m > k`. -/
theorem eq_zero_iff_forall_wCharge {k : ℕ} :
    k = 0 ↔ ∀ m : ℕ, wCharge (2 ^ m) (k : ℤ) = 0 := by
  constructor
  · rintro rfl m; simp [wCharge]
  · intro h
    have hk := h k
    haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
    rw [wCharge_eq_zero_iff] at hk
    have hkdvd : (2 ^ k : ℕ) ∣ k := by exact_mod_cast hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exact hk0
    · exact absurd (Nat.le_of_dvd hkpos hkdvd) (by simpa using Nat.lt_two_pow_self (n := k))

/-- **Inertia = Charge.**  For `k` distinct off-line poles `t_i ∈ ℂ⁺`, there is a node configuration
for which the FE seam Krein Gram is definite (`KreinNonneg`) **iff** the deck ladder charge of the
configuration vanishes at every rung `m`.  The analytic definiteness face (a positive polarization of
the FE-forced indefinite form) and the `2`-adic charge face (`∀ m, wCharge (2^m) (k : ℤ) = 0`) are one
condition; their common value is `k = 0` (no off-line zeros).  This welds `factoredKrein_kreinNonneg_iff`
(the Krein index) to the `DeckChargeCalculus` charge on a single object, with the surjectivity
hypothesis discharged. -/
theorem seam_inertia_eq_charge {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) :
    ∃ z : Fin (2 * k) → ℂ,
      KreinNonneg (factoredKreinForm (seamW t z) (seamU t z))
        ↔ ∀ m : ℕ, wCharge (2 ^ m) (k : ℤ) = 0 := by
  obtain ⟨z, hz⟩ := seamCarrier_kreinNonneg_iff t ht htinj
  exact ⟨z, hz.trans eq_zero_iff_forall_wCharge⟩

end

end RHTower
