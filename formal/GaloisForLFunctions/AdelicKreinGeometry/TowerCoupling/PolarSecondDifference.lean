import GaloisForLFunctions.AdelicKreinGeometry.TheSignatureOfASeparableAssembly
import GaloisForLFunctions.AdelicKreinGeometry.MixingKillsNegativeSquares
import GaloisForLFunctions.HeckeKreinToeplitz.ThePoleIsTheOnlyRemovableHyperbolicDirection

/-!
# The polar second-difference identity and polar trichotomy on `ℤ`

On `ℤ` the polar index `κ₀(k)` of a kernel—its negative index on the mean-zero hyperplane
`ker(totalMass)`—is governed by the centered second difference

  `Δ²k(m) = 2 k(m) − k(m + 1) − k(m − 1)`  (`secondDiff`).

* **Exact polar identity** (`polarIndex_eq_negIndex_secondDiff`): for every kernel
  `k : Multiplicative ℤ → ℂ`, `polarIndex k = negIndex (secondDiff k)`. Summation by parts via
  `diffMap M : (Fin M → ℂ) →ₗ[ℂ] (Fin (M + 1) → ℂ)` identifies `ker(totalMass)` on every contiguous
  integer grid with `Fin M → ℂ` and sends the Toeplitz form of `k` to that of `secondDiff k`.
* **Polar zero-or-infinity law** (`polarIndex_eq_zero_or_top_of_secondDiff_tendsto`): if `k` is
  Hermitian and `secondDiff k (ofAdd n) → 0` as `n → +∞`, then `polarIndex k ∈ {0, ⊤}`.
* **Polar trichotomy with a local pole** (`polarIndex_pairKernel_add_of_secondDiff_tendsto`): for
  `r > 1`, a local pole pair `pairKernel (valChar r) ω`, and a Hermitian remainder `g` whose second
  difference vanishes at `+∞`:
  - `polarIndex = ⊤` when `¬ IsPosDefKernel (secondDiff g)`;
  - `polarIndex = 0` when `IsPosDefKernel (secondDiff g)` and `ω = 0`;
  - `polarIndex = 1` when `IsPosDefKernel (secondDiff g)` and `ω ≠ 0`.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling

/-! ### The centered second difference on `ℤ` -/

/-- The centered second difference `Δ²k(m) = 2 k(m) − k(m + 1) − k(m − 1)` on `ℤ`. -/
def secondDiff (k : Multiplicative ℤ → ℂ) (m : Multiplicative ℤ) : ℂ :=
  2 * k m - k (m * Multiplicative.ofAdd 1) - k (m * Multiplicative.ofAdd (-1))

theorem isHermKernel_secondDiff {k : Multiplicative ℤ → ℂ} (hk : IsHermKernel k) :
    IsHermKernel (secondDiff k) := fun m => by
  have h1 : m⁻¹ * Multiplicative.ofAdd 1 = (m * Multiplicative.ofAdd (-1))⁻¹ := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    ring
  have h2 : m⁻¹ * Multiplicative.ofAdd (-1) = (m * Multiplicative.ofAdd 1)⁻¹ := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    ring
  show secondDiff k m⁻¹ = conj (secondDiff k m)
  simp only [secondDiff, h1, h2, hk m, hk (m * Multiplicative.ofAdd (-1)),
    hk (m * Multiplicative.ofAdd 1), map_sub, map_mul, Complex.conj_ofNat]
  ring

theorem secondDiff_add (f g : Multiplicative ℤ → ℂ) (m : Multiplicative ℤ) :
    secondDiff (fun x => f x + g x) m = secondDiff f m + secondDiff g m := by
  simp only [secondDiff]
  ring

theorem secondDiff_sub (f g : Multiplicative ℤ → ℂ) (m : Multiplicative ℤ) :
    secondDiff (fun x => f x - g x) m = secondDiff f m - secondDiff g m := by
  simp only [secondDiff]
  ring

theorem secondDiff_const_mul (c : ℂ) (k : Multiplicative ℤ → ℂ) (m : Multiplicative ℤ) :
    secondDiff (fun x => c * k x) m = c * secondDiff k m := by
  simp only [secondDiff]
  ring

theorem secondDiff_const (c : ℂ) (m : Multiplicative ℤ) :
    secondDiff (fun _ => c) m = 0 := by
  simp only [secondDiff]
  ring

/-- `Δ²(−|m|) = 0` for `m > 0`, and `2` at `m = 0`. -/
theorem secondDiff_negAbsKernel_of_pos {n : ℤ} (hn : 1 ≤ n) :
    secondDiff negAbsKernel (Multiplicative.ofAdd n) = 0 := by
  have h0 : 0 ≤ n := by omega
  have h1 : 0 ≤ n + 1 := by omega
  have h2 : 0 ≤ n + -1 := by omega
  simp only [secondDiff, negAbsKernel, ← ofAdd_add, toAdd_ofAdd, abs_of_nonneg h0,
    abs_of_nonneg h1, abs_of_nonneg h2]
  push_cast
  ring

/-- A Kronecker delta at the identity has vanishing second difference for `n ≥ 2`. -/
theorem secondDiff_deltaOne_of_two_le {n : ℤ} (hn : 2 ≤ n) (D : ℂ) :
    secondDiff (fun m => if m = 1 then D else 0) (Multiplicative.ofAdd n) = 0 := by
  have h0 : Multiplicative.ofAdd n ≠ 1 := fun h => by
    have := congrArg Multiplicative.toAdd h; simp at this; omega
  have h1 : Multiplicative.ofAdd n * Multiplicative.ofAdd 1 ≠ 1 := fun h => by
    have := congrArg Multiplicative.toAdd h; simp at this; omega
  have h2 : Multiplicative.ofAdd n * Multiplicative.ofAdd (-1) ≠ 1 := fun h => by
    have := congrArg Multiplicative.toAdd h; simp at this; omega
  simp only [secondDiff, if_neg h0, if_neg h1, if_neg h2]
  ring

/-! ### Summation by parts on contiguous integer grids -/

/-- The contiguous integer grid `L, L + 1, …, L + M` in `Multiplicative ℤ`. -/
def gridPts (L : ℤ) (M : ℕ) (a : Fin (M + 1)) : Multiplicative ℤ :=
  Multiplicative.ofAdd (L + (a : ℤ))

/-- The initial `M` points `L, L + 1, …, L + M − 1` of the contiguous grid. -/
def gridInit (L : ℤ) (M : ℕ) (i : Fin M) : Multiplicative ℤ :=
  Multiplicative.ofAdd (L + (i : ℤ))

/-- The elementary mean-zero step `e_i − e_{i+1}` on `Fin (M + 1)`. -/
def stepVec (M : ℕ) (i : Fin M) : Fin (M + 1) → ℂ :=
  Pi.single i.castSucc 1 - Pi.single i.succ 1

theorem sum_stepVec_mul (M : ℕ) (i : Fin M) (f : Fin (M + 1) → ℂ) :
    ∑ a : Fin (M + 1), stepVec M i a * f a = f i.castSucc - f i.succ := by
  simp only [stepVec, Pi.sub_apply, sub_mul, sum_sub_distrib, Pi.single_apply, ite_mul, one_mul,
    zero_mul, sum_ite_eq', mem_univ, if_true]

theorem sum_conj_stepVec_mul (M : ℕ) (i : Fin M) (f : Fin (M + 1) → ℂ) :
    ∑ a : Fin (M + 1), conj (stepVec M i a) * f a = f i.castSucc - f i.succ := by
  have hc : ∀ a, conj (stepVec M i a) = stepVec M i a := fun a => by
    simp only [stepVec, Pi.sub_apply, Pi.single_apply, map_sub]
    split_ifs <;> simp
  simp_rw [hc]
  exact sum_stepVec_mul M i f

/-- The discrete difference map `d ↦ Σ_{i < M} d_i (e_i − e_{i+1})`. -/
def diffMap (M : ℕ) : (Fin M → ℂ) →ₗ[ℂ] (Fin (M + 1) → ℂ) where
  toFun d := ∑ i : Fin M, d i • stepVec M i
  map_add' d₁ d₂ := by simp only [Pi.add_apply, add_smul, sum_add_distrib]
  map_smul' t d := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, smul_sum]

theorem sum_diffMap_mul (M : ℕ) (d : Fin M → ℂ) (f : Fin (M + 1) → ℂ) :
    ∑ a : Fin (M + 1), diffMap M d a * f a = ∑ i : Fin M, d i * (f i.castSucc - f i.succ) := by
  have heq : ∀ a, diffMap M d a * f a = ∑ i : Fin M, d i * (stepVec M i a * f a) := fun a => by
    simp only [diffMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, sum_mul, mul_assoc]
  simp_rw [heq]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => by rw [← mul_sum, sum_stepVec_mul]

theorem sum_conj_diffMap_mul (M : ℕ) (d : Fin M → ℂ) (f : Fin (M + 1) → ℂ) :
    ∑ a : Fin (M + 1), conj (diffMap M d a) * f a =
      ∑ i : Fin M, conj (d i) * (f i.castSucc - f i.succ) := by
  have heq : ∀ a, conj (diffMap M d a) * f a =
      ∑ i : Fin M, conj (d i) * (conj (stepVec M i a) * f a) := fun a => by
    simp only [diffMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, map_sum, map_mul, sum_mul, mul_assoc]
  simp_rw [heq]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => by rw [← mul_sum, sum_conj_stepVec_mul]

theorem diffMap_mem_ker_totalMass (M : ℕ) (d : Fin M → ℂ) :
    diffMap M d ∈ LinearMap.ker (totalMass (Fin (M + 1))) := by
  rw [LinearMap.mem_ker, totalMass]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have := sum_diffMap_mul M d (fun _ => 1)
  simpa using this

/-- The prefix-sum functional `c ↦ (Σ_{a ≤ i} c_a)_{i < M}`, left inverse to `diffMap M`. -/
def prefixSum (M : ℕ) : (Fin (M + 1) → ℂ) →ₗ[ℂ] (Fin M → ℂ) where
  toFun c i := ∑ a : Fin (M + 1), if (a : ℕ) ≤ (i : ℕ) then c a else 0
  map_add' c₁ c₂ := funext fun i => by
    simp only [Pi.add_apply, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by split_ifs <;> ring
  map_smul' t c := funext fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun a _ => by split_ifs <;> ring

theorem prefixSum_diffMap (M : ℕ) (d : Fin M → ℂ) : prefixSum M (diffMap M d) = d := by
  funext k
  have heq : prefixSum M (diffMap M d) k =
      ∑ a : Fin (M + 1), diffMap M d a * (if (a : ℕ) ≤ (k : ℕ) then (1 : ℂ) else 0) := by
    simp only [prefixSum, LinearMap.coe_mk, AddHom.coe_mk, mul_ite, mul_one, mul_zero]
  rw [heq, sum_diffMap_mul]
  have hdelta : ∀ i : Fin M,
      ((if (i.castSucc : ℕ) ≤ (k : ℕ) then (1 : ℂ) else 0) -
        (if (i.succ : ℕ) ≤ (k : ℕ) then 1 else 0)) = if i = k then 1 else 0 := fun i => by
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hik : i = k
    · subst hik
      rw [if_pos le_rfl, if_neg (by omega), if_pos rfl, sub_zero]
    · have hne : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
      rw [if_neg hik]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_pos hlt.le, if_pos (by omega), sub_self]
      · rw [if_neg (by omega), if_neg (by omega), sub_self]
  simp only [hdelta, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

theorem diffMap_injective (M : ℕ) : Function.Injective (diffMap M) :=
  Function.LeftInverse.injective (prefixSum_diffMap M)

theorem range_diffMap_eq_ker_totalMass (M : ℕ) :
    LinearMap.range (diffMap M) = LinearMap.ker (totalMass (Fin (M + 1))) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨d, rfl⟩
    exact diffMap_mem_ker_totalMass M d
  · have hsurj : Function.Surjective (totalMass (Fin (M + 1))) := fun z =>
      ⟨z • Pi.single 0 1, by simp [totalMass]⟩
    have hrk := LinearMap.finrank_range_add_finrank_ker (totalMass (Fin (M + 1)))
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
    rw [LinearMap.finrank_range_of_inj (diffMap_injective M),
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega

theorem diffMap_prefixSum_of_mem_ker (M : ℕ) {c : Fin (M + 1) → ℂ}
    (hc : c ∈ LinearMap.ker (totalMass (Fin (M + 1)))) :
    diffMap M (prefixSum M c) = c := by
  rw [← range_diffMap_eq_ker_totalMass M] at hc
  obtain ⟨d, rfl⟩ := hc
  rw [prefixSum_diffMap]

/-- **Summation by parts on a contiguous grid.** The Toeplitz form of `k` at `diffMap M d` is
the Toeplitz form of `secondDiff k` at `d`. -/
theorem hermQuad_gram_gridPts_diffMap (k : Multiplicative ℤ → ℂ) (L : ℤ) (M : ℕ) (d : Fin M → ℂ) :
    hermQuad (gram k (gridPts L M)) (diffMap M d) =
      hermQuad (gram (secondDiff k) (gridInit L M)) d := by
  rw [hermQuad_gram, hermQuad_gram]
  congr 1
  have hinner : ∀ a : Fin (M + 1),
      ∑ b : Fin (M + 1), conj (diffMap M d a) * k ((gridPts L M a)⁻¹ * gridPts L M b) *
          diffMap M d b =
        conj (diffMap M d a) * ∑ j : Fin M, d j *
          (k ((gridPts L M a)⁻¹ * gridPts L M j.castSucc) -
            k ((gridPts L M a)⁻¹ * gridPts L M j.succ)) := fun a => by
    rw [← sum_diffMap_mul M d (fun b => k ((gridPts L M a)⁻¹ * gridPts L M b)), mul_sum]
    exact sum_congr rfl fun b _ => by ring
  simp_rw [hinner]
  rw [sum_conj_diffMap_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  set m : Multiplicative ℤ := (gridInit L M i)⁻¹ * gridInit L M j
  have e00 : (gridPts L M i.castSucc)⁻¹ * gridPts L M j.castSucc = m := rfl
  have e01 : (gridPts L M i.castSucc)⁻¹ * gridPts L M j.succ = m * Multiplicative.ofAdd 1 := by
    apply Multiplicative.toAdd.injective
    simp only [gridPts, gridInit, m, Fin.val_castSucc, Fin.val_succ, toAdd_mul, toAdd_inv,
      toAdd_ofAdd]
    push_cast; ring
  have e10 : (gridPts L M i.succ)⁻¹ * gridPts L M j.castSucc = m * Multiplicative.ofAdd (-1) := by
    apply Multiplicative.toAdd.injective
    simp only [gridPts, gridInit, m, Fin.val_castSucc, Fin.val_succ, toAdd_mul, toAdd_inv,
      toAdd_ofAdd]
    push_cast; ring
  have e11 : (gridPts L M i.succ)⁻¹ * gridPts L M j.succ = m := by
    apply Multiplicative.toAdd.injective
    simp only [gridPts, gridInit, m, Fin.val_succ, toAdd_mul, toAdd_inv, toAdd_ofAdd]
    push_cast; ring
  rw [e00, e01, e10, e11, secondDiff]
  ring

/-! ### Pushing coefficient vectors along reindexings -/

/-- Pushforward of coefficient vectors `c ↦ (Σ_{f a = u} c_a)_u`. -/
def pushVec {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) : (α → ℂ) →ₗ[ℂ] (β → ℂ) where
  toFun c u := ∑ a : α, if f a = u then c a else 0
  map_add' c₁ c₂ := funext fun u => by
    simp only [Pi.add_apply, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by split_ifs <;> ring
  map_smul' t c := funext fun u => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl fun a _ => by split_ifs <;> ring

theorem totalMass_pushVec {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β)
    (c : α → ℂ) : totalMass β (pushVec f c) = totalMass α c := by
  simp only [totalMass, pushVec, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun a _ => by simp

theorem hermQuad_gram_pushVec {G : Type*} [Group G] {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (k : G → ℂ) (y : β → G) (f : α → β) (c : α → ℂ) :
    hermQuad (gram k y) (pushVec f c) = hermQuad (gram k (y ∘ f)) c := by
  rw [hermQuad_gram, hermQuad_gram]
  congr 1
  have hrow : ∀ u : β, ∑ v : β, conj (pushVec f c u) * k ((y u)⁻¹ * y v) * pushVec f c v =
      ∑ b : α, conj (pushVec f c u) * k ((y u)⁻¹ * y (f b)) * c b := fun u => by
    simp only [pushVec, LinearMap.coe_mk, AddHom.coe_mk, mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun b _ => ?_
    simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  have hcol : ∀ b : α, ∑ u : β, conj (pushVec f c u) * k ((y u)⁻¹ * y (f b)) * c b =
      ∑ a : α, conj (c a) * k ((y (f a))⁻¹ * y (f b)) * c b := fun b => by
    simp only [pushVec, LinearMap.coe_mk, AddHom.coe_mk, map_sum, sum_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    have : ∀ u : β, conj (if f a = u then c a else 0) * k ((y u)⁻¹ * y (f b)) * c b =
        if f a = u then conj (c a) * k ((y u)⁻¹ * y (f b)) * c b else 0 := fun u => by
      split_ifs <;> simp
    simp_rw [this]
    simp
  simp_rw [hcol]
  exact Finset.sum_comm

/-! ### The exact polar identity on `ℤ` -/

/-- **Polar second-difference identity.** On `ℤ`, the polar index of every kernel equals the
unconstrained negative index of its centered second difference. -/
theorem polarIndex_eq_negIndex_secondDiff (k : Multiplicative ℤ → ℂ) :
    polarIndex k = negIndex (secondDiff k) := by
  classical
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun n x => ?_
    set z : Fin n → ℤ := fun a => Multiplicative.toAdd (x a)
    set L : ℤ := -∑ a, |z a|
    have hL : ∀ a, L ≤ z a := fun a => by
      have h1 := single_le_sum (f := fun a => |z a|) (fun _ _ => abs_nonneg _) (mem_univ a)
      linarith [neg_abs_le (z a)]
    set w : Fin n → ℕ := fun a => (z a - L).toNat
    have hw : ∀ a, (w a : ℤ) = z a - L := fun a => Int.toNat_of_nonneg (by linarith [hL a])
    set M : ℕ := ∑ b, w b
    set f : Fin n → Fin (M + 1) := fun a =>
      ⟨w a, Nat.lt_succ_of_le (single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_univ a))⟩
    have hgf : gridPts L M ∘ f = x := funext fun a => by
      apply Multiplicative.toAdd.injective
      simp only [Function.comp_apply, gridPts, f, toAdd_ofAdd, hw, z]
      ring
    obtain ⟨W, hWV, hWr, hW⟩ := exists_negIndexOn (gram k x) (LinearMap.ker (totalMass (Fin n)))
    set bW := Module.finBasis ℂ W
    set Ψ : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (Fin M → ℂ) :=
      prefixSum M ∘ₗ pushVec f ∘ₗ W.subtype ∘ₗ bW.equivFun.symm.toLinearMap
    have hneg : ∀ β, β ≠ 0 → hermQuad (gram (secondDiff k) (gridInit L M)) (Ψ β) < 0 := by
      intro β hβ
      set c : W := bW.equivFun.symm β
      have hc0 : (c : Fin n → ℂ) ≠ 0 := fun h =>
        hβ (bW.equivFun.symm.injective ((Subtype.ext h).trans (map_zero _).symm))
      have hc_ker : pushVec f (c : Fin n → ℂ) ∈ LinearMap.ker (totalMass (Fin (M + 1))) := by
        rw [LinearMap.mem_ker, totalMass_pushVec]
        exact LinearMap.mem_ker.mp (hWV c.2)
      have hquad : hermQuad (gram (secondDiff k) (gridInit L M)) (Ψ β) =
          hermQuad (gram k x) (c : Fin n → ℂ) := by
        simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
          LinearEquiv.coe_coe, c]
        rw [← hermQuad_gram_gridPts_diffMap, diffMap_prefixSum_of_mem_ker M hc_ker,
          hermQuad_gram_pushVec, hgf]
      rw [hquad]
      have hpos := hW _ c.2 hc0
      rw [hermQuad_neg] at hpos
      linarith
    have h := card_le_hermNegIndex_of_forall_neg _ Ψ hneg
    rw [Fintype.card_fin, hWr] at h
    exact (Nat.cast_le.mpr h).trans (hermNegIndex_gram_le_negIndex _ _)
  · refine negIndex_le_iff.mpr fun m y => ?_
    set z : Fin m → ℤ := fun a => Multiplicative.toAdd (y a)
    set L : ℤ := -∑ a, |z a|
    have hL : ∀ a, L ≤ z a := fun a => by
      have h1 := single_le_sum (f := fun a => |z a|) (fun _ _ => abs_nonneg _) (mem_univ a)
      linarith [neg_abs_le (z a)]
    set w : Fin m → ℕ := fun a => (z a - L).toNat
    have hw : ∀ a, (w a : ℤ) = z a - L := fun a => Int.toNat_of_nonneg (by linarith [hL a])
    set M : ℕ := (∑ b, w b) + 1
    set f : Fin m → Fin M := fun a =>
      ⟨w a, Nat.lt_succ_of_le (single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_univ a))⟩
    have hgf : gridInit L M ∘ f = y := funext fun a => by
      apply Multiplicative.toAdd.injective
      simp only [Function.comp_apply, gridInit, f, toAdd_ofAdd, hw, z]
      ring
    obtain ⟨W, hWr, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-gram (secondDiff k) y)
    set bW := Module.finBasis ℂ W
    set Φ : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (Fin (M + 1) → ℂ) :=
      diffMap M ∘ₗ pushVec f ∘ₗ W.subtype ∘ₗ bW.equivFun.symm.toLinearMap
    have hneg : ∀ β, β ≠ 0 → hermQuad (gram k (gridPts L M)) (Φ β) < 0 := by
      intro β hβ
      set d : W := bW.equivFun.symm β
      have hd0 : (d : Fin m → ℂ) ≠ 0 := fun h =>
        hβ (bW.equivFun.symm.injective ((Subtype.ext h).trans (map_zero _).symm))
      have hquad : hermQuad (gram k (gridPts L M)) (Φ β) =
          hermQuad (gram (secondDiff k) y) (d : Fin m → ℂ) := by
        simp only [Φ, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
          LinearEquiv.coe_coe, d]
        rw [hermQuad_gram_gridPts_diffMap, hermQuad_gram_pushVec, hgf]
      rw [hquad]
      have hpos := hW _ d.2 hd0
      rw [hermQuad_neg] at hpos
      linarith
    have h := card_le_negIndexOn_of_forall_neg (gram k (gridPts L M))
      (LinearMap.ker (totalMass (Fin (M + 1)))) Φ
      (fun β => diffMap_mem_ker_totalMass M _) hneg
    rw [Fintype.card_fin] at h
    have h2 : hermNegIndex (gram (secondDiff k) y) = Module.finrank ℂ W := hWr.symm
    calc (hermNegIndex (gram (secondDiff k) y) : ℕ∞)
        ≤ (negIndexOn (gram k (gridPts L M)) (LinearMap.ker (totalMass (Fin (M + 1)))) : ℕ∞) :=
          Nat.cast_le.mpr (h2 ▸ h)
      _ ≤ polarIndex k := negIndexOn_le_polarIndex k (gridPts L M)

/-- **Polar zero-or-infinity law.** If `k` is Hermitian and `secondDiff k` vanishes at `+∞`,
then `polarIndex k` is `0` or `⊤`. -/
theorem polarIndex_eq_zero_or_top_of_secondDiff_tendsto {k : Multiplicative ℤ → ℂ}
    (hk : IsHermKernel k)
    (h0 : Tendsto (fun n : ℤ => secondDiff k (Multiplicative.ofAdd n)) atTop (𝓝 0)) :
    polarIndex k = 0 ∨ polarIndex k = ⊤ := by
  rw [polarIndex_eq_negIndex_secondDiff]
  exact negIndex_eq_zero_or_top_of_tendsto_int (isHermKernel_secondDiff hk) h0

/-! ### The polar trichotomy with a local pole -/

/-- On `ℤ`, `Δ²` acts on a real hyperbolic pair `pairKernel (valChar r) ω` by multiplying the
weight by `2 − r − r⁻¹ = −(r − 1)² / r`. -/
theorem secondDiff_pairKernel_valChar_real {r : ℝ} (hr : r ≠ 0) (ω : ℂ) :
    secondDiff (pairKernel (valChar (r : ℂ)) ω) =
      pairKernel (valChar (r : ℂ)) (((2 - r - r⁻¹ : ℝ) : ℂ) * ω) := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hrinv : ((r : ℂ))⁻¹ ≠ 0 := inv_ne_zero hrc
  funext m
  have hrefl : ∀ x, reflectChar (valChar (r : ℂ)) x = valChar ((r : ℂ))⁻¹ x := fun x => by
    rw [reflectChar_valChar hrc, Complex.conj_ofReal]
  have hval : ∀ (v : ℂ), v ≠ 0 → ∀ x, valChar v x = v ^ Multiplicative.toAdd x := fun v hv x => by
    simp [valChar, hv]
  simp only [secondDiff, pairKernel, hrefl, hval (r : ℂ) hrc, hval ((r : ℂ))⁻¹ hrinv,
    toAdd_mul, toAdd_ofAdd, zpow_add₀ hrc, zpow_add₀ hrinv, zpow_one, zpow_neg_one, inv_inv,
    map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- Adding a single hyperbolic pair changes the unconstrained negative index by at most one. -/
theorem negIndex_le_add_pairKernel_add_one {G : Type*} [Group G] (p : G → ℂ) (χ : G →* ℂ)
    (ω : ℂ) : negIndex p ≤ negIndex (fun u => p u + pairKernel χ ω u) + 1 := by
  refine negIndex_le_iff.mpr fun n x => ?_
  have h := hermNegIndex_le_add_one_of_eq_on_ker (gram p x)
    (gram (fun u => p u + pairKernel χ ω u) x) (charEval χ x) fun c hc => by
      rw [hermQuad_gram_add, hermQuad_gram_pairKernel, hc]
      simp
  calc (hermNegIndex (gram p x) : ℕ∞)
      ≤ (hermNegIndex (gram (fun u => p u + pairKernel χ ω u) x) : ℕ∞) + 1 := by exact_mod_cast h
    _ ≤ negIndex (fun u => p u + pairKernel χ ω u) + 1 := by
        gcongr; exact hermNegIndex_gram_le_negIndex _ x

/-- **The polar trichotomy on `ℤ`.** Let `r > 1`, `ω ∈ ℂ`, and let `g : Multiplicative ℤ → ℂ` be a
Hermitian kernel whose second difference tends to `0` at `+∞`. Then the polar index of
`pairKernel (valChar r) ω + g` is:
* `⊤` if `secondDiff g` is not positive definite;
* `0` if `secondDiff g` is positive definite and `ω = 0`;
* `1` if `secondDiff g` is positive definite and `ω ≠ 0`. -/
theorem polarIndex_pairKernel_add_of_secondDiff_tendsto {r : ℝ} (hr : 1 < r) (ω : ℂ)
    {g : Multiplicative ℤ → ℂ} (hg : IsHermKernel g)
    (hg0 : Tendsto (fun n : ℤ => secondDiff g (Multiplicative.ofAdd n)) atTop (𝓝 0)) :
    (¬ IsPosDefKernel (secondDiff g) →
        polarIndex (fun m => pairKernel (valChar (r : ℂ)) ω m + g m) = ⊤) ∧
      (IsPosDefKernel (secondDiff g) → ω = 0 →
        polarIndex (fun m => pairKernel (valChar (r : ℂ)) ω m + g m) = 0) ∧
      (IsPosDefKernel (secondDiff g) → ω ≠ 0 →
        polarIndex (fun m => pairKernel (valChar (r : ℂ)) ω m + g m) = 1) := by
  have hr0 : r ≠ 0 := by linarith
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
  set ω' : ℂ := ((2 - r - r⁻¹ : ℝ) : ℂ) * ω
  have hmult_ne : (2 - r - r⁻¹ : ℝ) ≠ 0 := by
    intro h
    have h1 : r * (2 - r - r⁻¹) = -(r - 1) ^ 2 := by field_simp [hr0]; ring
    rw [h, mul_zero] at h1
    nlinarith
  have hsd : secondDiff (fun m => pairKernel (valChar (r : ℂ)) ω m + g m) =
      fun m => secondDiff g m + pairKernel (valChar (r : ℂ)) ω' m := by
    funext m
    rw [secondDiff_add, secondDiff_pairKernel_valChar_real hr0 ω, add_comm]
  refine ⟨fun hnot => ?_, fun hpos hω0 => ?_, fun hpos hω => ?_⟩
  · rw [polarIndex_eq_negIndex_secondDiff, hsd]
    have hsd_herm : IsHermKernel (secondDiff g) := isHermKernel_secondDiff hg
    rcases negIndex_eq_zero_or_top_of_tendsto_int hsd_herm hg0 with hz | htop
    · exact absurd ((isPosDefKernel_iff hsd_herm).mpr hz) hnot
    · have hle := negIndex_le_add_pairKernel_add_one (secondDiff g) (valChar (r : ℂ)) ω'
      rw [htop, top_le_iff] at hle
      by_contra hfin
      have : negIndex (fun u => secondDiff g u + pairKernel (valChar (r : ℂ)) ω' u) + 1 < ⊤ :=
        ENat.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hfin, ENat.coe_lt_top 1⟩
      exact this.ne hle
  · rw [polarIndex_eq_negIndex_secondDiff, hsd]
    have hω'0 : ω' = 0 := by simp [ω', hω0]
    have heq : (fun m => secondDiff g m + pairKernel (valChar (r : ℂ)) ω' m) = secondDiff g := by
      funext m; simp [pairKernel, hω'0]
    rw [heq]
    exact hpos.negIndex_eq_zero
  · rw [polarIndex_eq_negIndex_secondDiff, hsd]
    have hω' : ω' ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hmult_ne) hω
    have heq : (fun m => secondDiff g m + pairKernel (valChar (r : ℂ)) ω' m) =
        fun m => secondDiff g m + ∑ _j : Fin 1, pairKernel (valChar (r : ℂ)) ω' m := by
      funext m; simp
    rw [heq]
    refine le_antisymm ?_ ?_
    · simpa using negIndex_add_sum_pairKernel_le (J := Fin 1) hpos
        (fun _ => valChar (r : ℂ)) (fun _ => ω')
    · have hout : ∀ _j : Fin 1, 1 < ‖valChar (r : ℂ) (Multiplicative.ofAdd 1)‖ := fun _ => by
        rw [norm_valChar hrc, toAdd_ofAdd, zpow_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        exact hr
      have hsep : Function.Injective
          (nodes (κ := 1) (fun _ => valChar (r : ℂ)) (Multiplicative.ofAdd 1)) := by
        intro x y hxy
        rcases x with i | i <;> rcases y with j | j
        · exact congrArg Sum.inl (Subsingleton.elim i j)
        · exfalso
          simp only [nodes, Sum.elim_inl, Sum.elim_inr, reflectChar_valChar hrc,
            Complex.conj_ofReal] at hxy
          have hnorm := congrArg norm hxy
          rw [norm_valChar hrc, norm_valChar (inv_ne_zero hrc), toAdd_ofAdd, zpow_one, zpow_one,
            norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hnorm
          have : r * r = 1 := by field_simp [hr0] at hnorm; linarith
          nlinarith
        · exfalso
          simp only [nodes, Sum.elim_inl, Sum.elim_inr, reflectChar_valChar hrc,
            Complex.conj_ofReal] at hxy
          have hnorm := congrArg norm hxy
          rw [norm_valChar hrc, norm_valChar (inv_ne_zero hrc), toAdd_ofAdd, zpow_one, zpow_one,
            norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hnorm
          have : r * r = 1 := by field_simp [hr0] at hnorm; linarith
          nlinarith
        · exact congrArg Sum.inr (Subsingleton.elim i j)
      simpa using le_negIndex_of_separated_out (κ := 1) hpos (fun _ => valChar (r : ℂ))
        (fun _ => ω') (fun _ => hω') (Multiplicative.ofAdd 1) hout hsep

/-- Under the hypotheses of the polar trichotomy, the polar index always lies in `{0, 1, ⊤}`. -/
theorem polarIndex_pairKernel_add_mem {r : ℝ} (hr : 1 < r) (ω : ℂ) {g : Multiplicative ℤ → ℂ}
    (hg : IsHermKernel g)
    (hg0 : Tendsto (fun n : ℤ => secondDiff g (Multiplicative.ofAdd n)) atTop (𝓝 0)) :
    polarIndex (fun m => pairKernel (valChar (r : ℂ)) ω m + g m) ∈ ({0, 1, ⊤} : Set ℕ∞) := by
  obtain ⟨h1, h2, h3⟩ := polarIndex_pairKernel_add_of_secondDiff_tendsto hr ω hg hg0
  by_cases hp : IsPosDefKernel (secondDiff g)
  · by_cases hω : ω = 0
    · simp [h2 hp hω]
    · simp [h3 hp hω]
  · simp [h1 hp]

end GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling
