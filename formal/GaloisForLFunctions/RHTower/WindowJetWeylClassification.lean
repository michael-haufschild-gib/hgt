import GaloisForLFunctions.RHTower.FixedWindowWeylRigidity
import GaloisForLFunctions.RHTower.ShiftPairLocalIntersectionAlgebra

noncomputable section

namespace GaloisForLFunctions
namespace RHTower
namespace WindowJetWeylClassification

open GaloisForLFunctions.RHTower.FixedWindowWeylRigidity

def tailShift (m r : ℕ) : Module.End ℂ (Fin m → ℂ) where
  toFun v j := if h : (j : ℕ) + r < m then v ⟨(j : ℕ) + r, h⟩ else 0
  map_add' v w := by
    ext j
    by_cases h : (j : ℕ) + r < m <;> simp [h]
  map_smul' c v := by
    ext j
    by_cases h : (j : ℕ) + r < m <;> simp [h]

@[simp] theorem tailShift_apply_of_lt {m r : ℕ} (v : Fin m → ℂ) (j : Fin m)
    (h : (j : ℕ) + r < m) :
    tailShift m r v j = v ⟨(j : ℕ) + r, h⟩ := by
  simp [tailShift, h]

@[simp] theorem tailShift_apply_of_not_lt {m r : ℕ} (v : Fin m → ℂ) (j : Fin m)
    (h : ¬ (j : ℕ) + r < m) :
    tailShift m r v j = 0 := by
  simp [tailShift, h]

theorem tailShift_zero (m : ℕ) : tailShift m 0 = 1 := by
  ext v j
  simp [tailShift]

theorem tailShift_add (m a b : ℕ) :
    tailShift m a * tailShift m b = tailShift m (a + b) := by
  apply LinearMap.ext
  intro v
  funext j
  change tailShift m a (tailShift m b v) j = tailShift m (a + b) v j
  by_cases hab : (j : ℕ) + (a + b) < m
  · have ha : (j : ℕ) + a < m := by omega
    have hb : ((⟨(j : ℕ) + a, ha⟩ : Fin m) : ℕ) + b < m := by
      change (j : ℕ) + a + b < m
      omega
    rw [tailShift_apply_of_lt _ _ ha, tailShift_apply_of_lt _ _ hb,
      tailShift_apply_of_lt _ _ hab]
    apply congrArg v
    apply Fin.ext
    change (j : ℕ) + a + b = (j : ℕ) + (a + b)
    omega
  · by_cases ha : (j : ℕ) + a < m
    · have hb : ¬ ((⟨(j : ℕ) + a, ha⟩ : Fin m) : ℕ) + b < m := by
        change ¬ ((j : ℕ) + a + b < m)
        omega
      rw [tailShift_apply_of_lt _ _ ha, tailShift_apply_of_not_lt _ _ hb,
        tailShift_apply_of_not_lt _ _ hab]
    · rw [tailShift_apply_of_not_lt _ _ ha, tailShift_apply_of_not_lt _ _ hab]

theorem tailShift_one_pow (m n : ℕ) :
    (tailShift m 1) ^ n = tailShift m n := by
  induction n with
  | zero => simp [tailShift_zero]
  | succ n ih =>
      rw [pow_succ, ih, tailShift_add]

theorem mem_ker_tailShift_iff (m n : ℕ) (v : Fin m → ℂ) :
    v ∈ LinearMap.ker (tailShift m n) ↔
      ∀ j : Fin m, n ≤ (j : ℕ) → v j = 0 := by
  constructor
  · intro hv j hj
    have hjsub : (j : ℕ) - n + n = (j : ℕ) := Nat.sub_add_cancel hj
    have hlt : (j : ℕ) - n + n < m := by omega
    have hz := congrFun hv (⟨(j : ℕ) - n, by omega⟩ : Fin m)
    simpa [tailShift, hlt, hjsub] using hz
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext j
    by_cases h : (j : ℕ) + n < m
    · have hidx : n ≤ ((⟨(j : ℕ) + n, h⟩ : Fin m) : ℕ) := by
        change n ≤ (j : ℕ) + n
        omega
      have hz : v (⟨(j : ℕ) + n, h⟩ : Fin m) = 0 := hv _ hidx
      simpa [tailShift, h] using hz
    · simp [tailShift, h]

def initialSegmentEquiv (m n : ℕ) :
    (Fin (min n m) → ℂ) ≃ₗ[ℂ] LinearMap.ker (tailShift m n) where
  toFun v := ⟨fun j => if h : (j : ℕ) < min n m then v ⟨j, h⟩ else 0, by
    rw [mem_ker_tailShift_iff]
    intro j hj
    have hn : ¬ (j : ℕ) < min n m := by omega
    simp [hn]⟩
  invFun v j := v.1 ⟨j, by omega⟩
  left_inv v := by
    ext j
    change (if h : (j : ℕ) < min n m then v ⟨j, h⟩ else 0) = v j
    rw [dif_pos j.isLt]
  right_inv v := by
    apply Subtype.ext
    funext j
    by_cases h : (j : ℕ) < min n m
    · simp [h]
    · have hj : n ≤ (j : ℕ) := by omega
      simp [h, (mem_ker_tailShift_iff m n v.1).mp v.2 j hj]
  map_add' v w := by
    apply Subtype.ext
    funext j
    change (if h : (j : ℕ) < min n m then (v + w) ⟨j, h⟩ else 0) =
      (if h : (j : ℕ) < min n m then v ⟨j, h⟩ else 0) +
        if h : (j : ℕ) < min n m then w ⟨j, h⟩ else 0
    by_cases h : (j : ℕ) < min n m
    · simp only [dif_pos h, Pi.add_apply]
    · simp only [dif_neg h, add_zero]
  map_smul' c v := by
    apply Subtype.ext
    funext j
    change (if h : (j : ℕ) < min n m then (c • v) ⟨j, h⟩ else 0) =
      c • if h : (j : ℕ) < min n m then v ⟨j, h⟩ else 0
    by_cases h : (j : ℕ) < min n m
    · simp only [dif_pos h, Pi.smul_apply]
    · simp only [dif_neg h, smul_zero]

theorem finrank_ker_tailShift (m n : ℕ) :
    Module.finrank ℂ (LinearMap.ker (tailShift m n)) = min n m := by
  rw [← (initialSegmentEquiv m n).finrank_eq]
  simp

def blockTailShift {ι : Type*} (m : ι → ℕ) (r : ℕ) :
    Module.End ℂ ((i : ι) → Fin (m i) → ℂ) where
  toFun v i := tailShift (m i) r (v i)
  map_add' v w := by
    funext i
    exact (tailShift (m i) r).map_add (v i) (w i)
  map_smul' c v := by
    funext i
    exact (tailShift (m i) r).map_smul c (v i)

@[simp] theorem blockTailShift_apply {ι : Type*} (m : ι → ℕ) (r : ℕ)
    (v : (i : ι) → Fin (m i) → ℂ) (i : ι) :
    blockTailShift m r v i = tailShift (m i) r (v i) := rfl

theorem blockTailShift_add {ι : Type*} (m : ι → ℕ) (a b : ℕ) :
    blockTailShift m a * blockTailShift m b = blockTailShift m (a + b) := by
  apply LinearMap.ext
  intro v
  funext i
  exact LinearMap.congr_fun (tailShift_add (m i) a b) (v i)

theorem blockTailShift_zero {ι : Type*} (m : ι → ℕ) :
    blockTailShift m 0 = 1 := by
  apply LinearMap.ext
  intro v
  funext i
  exact LinearMap.congr_fun (tailShift_zero (m i)) (v i)

theorem blockTailShift_one_pow {ι : Type*} (m : ι → ℕ) (n : ℕ) :
    (blockTailShift m 1) ^ n = blockTailShift m n := by
  induction n with
  | zero => rw [pow_zero, blockTailShift_zero]
  | succ n ih => rw [pow_succ, ih, blockTailShift_add]

def blockKerEquiv {ι : Type*} (m : ι → ℕ) (n : ℕ) :
    LinearMap.ker (blockTailShift m n) ≃ₗ[ℂ]
      ((i : ι) → LinearMap.ker (tailShift (m i) n)) where
  toFun v i := ⟨v.1 i, by
    apply LinearMap.mem_ker.mpr
    have hv := LinearMap.mem_ker.mp v.2
    exact congrFun hv i⟩
  invFun v := ⟨fun i => (v i).1, by
    apply LinearMap.mem_ker.mpr
    funext i
    exact LinearMap.mem_ker.mp (v i).2⟩
  left_inv v := by rfl
  right_inv v := by rfl
  map_add' v w := by rfl
  map_smul' c v := by rfl

theorem finrank_ker_blockTailShift {ι : Type*} [Fintype ι] (m : ι → ℕ) (n : ℕ) :
    Module.finrank ℂ (LinearMap.ker (blockTailShift m n)) =
      ∑ i, min n (m i) := by
  rw [(blockKerEquiv m n).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp_rw [finrank_ker_tailShift]

theorem tailShift_self_eq_zero (m : ℕ) : tailShift m m = 0 := by
  apply LinearMap.ext
  intro v
  funext j
  exact tailShift_apply_of_not_lt v j (by omega)

def localJordan (m : ℕ) (μ : ℂ) : Module.End ℂ (Fin m → ℂ) :=
  μ • 1 + tailShift m 1

@[simp] theorem localJordan_apply (m : ℕ) (μ : ℂ) (v : Fin m → ℂ) (j : Fin m) :
    localJordan m μ v j = μ * v j +
      if h : (j : ℕ) + 1 < m then v ⟨(j : ℕ) + 1, h⟩ else 0 := by
  simp [localJordan, tailShift]

theorem localJordan_sub (m : ℕ) (μ nu : ℂ) :
    localJordan m μ - nu • 1 = (μ - nu) • 1 + tailShift m 1 := by
  ext v j
  simp [localJordan]
  ring

def localJordanLeftInverse (m : ℕ) (a : ℂ) : Module.End ℂ (Fin m → ℂ) :=
  let x : Module.End ℂ (Fin m → ℂ) := (-a⁻¹) • tailShift m 1
  (∑ i ∈ Finset.range m, x ^ i) * (a⁻¹ • 1)

theorem localJordanLeftInverse_mul (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    localJordanLeftInverse m a * (a • 1 + tailShift m 1) = 1 := by
  let N := tailShift m 1
  let x : Module.End ℂ (Fin m → ℂ) := (-a⁻¹) • N
  let S : Module.End ℂ (Fin m → ℂ) := ∑ i ∈ Finset.range m, x ^ i
  have hxpow : x ^ m = 0 := by
    rw [show x = (-a⁻¹) • N by rfl, smul_pow, show N = tailShift m 1 by rfl,
      tailShift_one_pow, tailShift_self_eq_zero, smul_zero]
  have hgeom : S * (1 - x) = 1 := by
    rw [show S = ∑ i ∈ Finset.range m, x ^ i by rfl, geom_sum_mul_neg, hxpow, sub_zero]
  have hscale : (a⁻¹ • (1 : Module.End ℂ (Fin m → ℂ))) *
      (a • 1 + N) = 1 - x := by
    ext v j
    simp [x, N]
    field_simp
  change S * (a⁻¹ • 1) * (a • 1 + N) = 1
  rw [mul_assoc, hscale, hgeom]

theorem localJordan_injective_of_ne_zero (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    Function.Injective (a • (1 : Module.End ℂ (Fin m → ℂ)) + tailShift m 1) := by
  rw [← LinearMap.ker_eq_bot]
  exact LinearMap.ker_eq_bot_of_inverse (localJordanLeftInverse_mul m ha)

theorem localJordan_pow_injective_of_ne_zero (m n : ℕ) {a : ℂ} (ha : a ≠ 0) :
    Function.Injective ((a • (1 : Module.End ℂ (Fin m → ℂ)) + tailShift m 1) ^ n) := by
  let L : Module.End ℂ (Fin m → ℂ) := a • 1 + tailShift m 1
  have hL : Function.Injective L := localJordan_injective_of_ne_zero m ha
  change Function.Injective (L ^ n)
  induction n with
  | zero =>
      intro v w h
      simpa using h
  | succ n ih =>
      intro v w h
      rw [pow_succ] at h
      change (L ^ n) (L v) = (L ^ n) (L w) at h
      apply hL
      exact ih h

theorem finrank_ker_localJordan_sub_pow (m n : ℕ) (μ nu : ℂ) :
    Module.finrank ℂ (LinearMap.ker ((localJordan m μ - nu • 1) ^ n)) =
      if μ = nu then min n m else 0 := by
  rw [localJordan_sub]
  by_cases h : μ = nu
  · subst nu
    rw [sub_self, zero_smul, zero_add, tailShift_one_pow]
    rw [finrank_ker_tailShift]
    simp
  · rw [if_neg h]
    have hne : μ - nu ≠ 0 := sub_ne_zero.mpr h
    rw [show LinearMap.ker (((μ - nu) • (1 : Module.End ℂ (Fin m → ℂ)) + tailShift m 1) ^ n) = ⊥ by
      exact LinearMap.ker_eq_bot.mpr (localJordan_pow_injective_of_ne_zero m n hne)]
    simp

def blockJordan {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ) :
    Module.End ℂ ((i : ι) → Fin (m i) → ℂ) where
  toFun v i := localJordan (m i) (μ i) (v i)
  map_add' v w := by
    funext i
    exact (localJordan (m i) (μ i)).map_add (v i) (w i)
  map_smul' c v := by
    funext i
    exact (localJordan (m i) (μ i)).map_smul c (v i)

@[simp] theorem blockJordan_apply {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (v : (i : ι) → Fin (m i) → ℂ) (i : ι) :
    blockJordan m μ v i = localJordan (m i) (μ i) (v i) := rfl

theorem blockJordan_pencil_pow_apply {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (nu : ℂ) (n : ℕ) (v : (i : ι) → Fin (m i) → ℂ) (i : ι) :
    ((blockJordan m μ - nu • 1) ^ n) v i =
      ((localJordan (m i) (μ i) - nu • 1) ^ n) (v i) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change ((blockJordan m μ - nu • 1) ^ n)
          ((blockJordan m μ - nu • 1) v) i =
        ((localJordan (m i) (μ i) - nu • 1) ^ n)
          ((localJordan (m i) (μ i) - nu • 1) (v i))
      rw [ih]
      rfl

def blockJordanKerEquiv {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ) (nu : ℂ) (n : ℕ) :
    LinearMap.ker ((blockJordan m μ - nu • 1) ^ n) ≃ₗ[ℂ]
      ((i : ι) → LinearMap.ker ((localJordan (m i) (μ i) - nu • 1) ^ n)) where
  toFun v i := ⟨v.1 i, by
    apply LinearMap.mem_ker.mpr
    have hv := LinearMap.mem_ker.mp v.2
    have hi := congrFun hv i
    rwa [blockJordan_pencil_pow_apply] at hi⟩
  invFun v := ⟨fun i => (v i).1, by
    apply LinearMap.mem_ker.mpr
    funext i
    rw [blockJordan_pencil_pow_apply]
    exact LinearMap.mem_ker.mp (v i).2⟩
  left_inv v := by rfl
  right_inv v := by rfl
  map_add' v w := by rfl
  map_smul' c v := by rfl

theorem finrank_ker_blockJordan_pencil_pow {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (nu : ℂ) (n : ℕ) :
    Module.finrank ℂ (LinearMap.ker ((blockJordan m μ - nu • 1) ^ n)) =
      ∑ i, if μ i = nu then min n (m i) else 0 := by
  rw [(blockJordanKerEquiv m μ nu n).finrank_eq, Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact finrank_ker_localJordan_sub_pow (m i) n (μ i) nu

noncomputable def kernelProfile {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (nu : ℂ) (n : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker ((T - nu • 1) ^ n))

theorem kernelProfile_conj {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (e : V ≃ₗ[ℂ] V) (T : Module.End ℂ V) (nu : ℂ) (n : ℕ) :
    kernelProfile (e.conj T) nu n = kernelProfile T nu n := by
  unfold kernelProfile
  rw [← GaloisForLFunctions.RHTower.FixedWindowWeylRigidity.conj_sub_smul_one,
    ← GaloisForLFunctions.RHTower.FixedWindowWeylRigidity.conj_pow,
    GaloisForLFunctions.RHTower.FixedWindowWeylRigidity.ker_conj]
  exact LinearEquiv.finrank_map_eq e _

theorem kernelProfile_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {zeta : ℂ} (hzeta : zeta ≠ 0)
    (T : Module.End ℂ V) (nu : ℂ) (n : ℕ) :
    kernelProfile (zeta • T) nu n = kernelProfile T (nu / zeta) n := by
  unfold kernelProfile
  have hpencil : zeta • T - nu • (1 : Module.End ℂ V) =
      zeta • (T - (nu / zeta) • (1 : Module.End ℂ V)) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ nu hzeta]
  rw [hpencil, smul_pow, LinearMap.ker_smul _ _ (pow_ne_zero _ hzeta)]

theorem kernelProfile_rotation {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {W : V ≃ₗ[ℂ] V} {T : Module.End ℂ V}
    {zeta : ℂ} (hzeta : zeta ≠ 0) (hW : W.conj T = zeta • T)
    (nu : ℂ) (n : ℕ) :
    kernelProfile T (zeta * nu) n = kernelProfile T nu n := by
  have h := (kernelProfile_conj W T (zeta * nu) n).symm
  rw [hW, kernelProfile_smul hzeta] at h
  rwa [mul_div_cancel_left₀ nu hzeta] at h

def jordanProfile {ι : Type*} [Fintype ι] (μ : ι → ℂ) (m : ι → ℕ)
    (nu : ℂ) (n : ℕ) : ℕ :=
  ∑ i, if μ i = nu then min n (m i) else 0

theorem kernelProfile_blockJordan {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (nu : ℂ) (n : ℕ) :
    kernelProfile (blockJordan m μ) nu n = jordanProfile μ m nu n := by
  exact finrank_ker_blockJordan_pencil_pow m μ nu n

def jordanLargeCount {ι : Type*} [Fintype ι] (μ : ι → ℂ) (m : ι → ℕ)
    (nu : ℂ) (n : ℕ) : ℕ :=
  ∑ i, if μ i = nu ∧ n < m i then 1 else 0

def jordanPairCount {ι : Type*} [Fintype ι] (μ : ι → ℂ) (m : ι → ℕ)
    (nu : ℂ) (q : ℕ) : ℕ :=
  ∑ i, if μ i = nu ∧ m i = q then 1 else 0

lemma min_succ_eq_min_add_indicator (n q : ℕ) :
    min (n + 1) q = min n q + if n < q then 1 else 0 := by
  by_cases h : n < q <;> simp [h] <;> omega

theorem jordanProfile_succ {ι : Type*} [Fintype ι] (μ : ι → ℂ) (m : ι → ℕ)
    (nu : ℂ) (n : ℕ) :
    jordanProfile μ m nu (n + 1) =
      jordanProfile μ m nu n + jordanLargeCount μ m nu n := by
  classical
  unfold jordanProfile jordanLargeCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hμ : μ i = nu
  · simp only [hμ, ↓reduceIte, true_and]
    exact min_succ_eq_min_add_indicator n (m i)
  · simp [hμ]

theorem jordanLargeCount_eq_of_profile_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → ℂ) (m : ι → ℕ) (ν : κ → ℂ) (q : κ → ℕ)
    (hprofile : ∀ z n, jordanProfile μ m z n = jordanProfile ν q z n)
    (z : ℂ) (n : ℕ) :
    jordanLargeCount μ m z n = jordanLargeCount ν q z n := by
  have hs := hprofile z (n + 1)
  have hn := hprofile z n
  rw [jordanProfile_succ, jordanProfile_succ, hn] at hs
  omega

theorem jordanLargeCount_pred (μ : ι → ℂ) (m : ι → ℕ) [Fintype ι]
    (nu : ℂ) {q : ℕ} (hq : 0 < q) :
    jordanLargeCount μ m nu (q - 1) =
      jordanPairCount μ m nu q + jordanLargeCount μ m nu q := by
  classical
  unfold jordanLargeCount jordanPairCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hμ : μ i = nu
  · simp only [hμ, true_and]
    by_cases hm : m i = q
    · subst q
      simp [hq]
    · by_cases hlt : q < m i
      · have hpred : q - 1 < m i := by omega
        simp [hm, hlt, hpred]
      · have hpred : ¬ q - 1 < m i := by omega
        simp [hm, hlt, hpred]
  · simp [hμ]

theorem jordanPairCount_eq_of_profile_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → ℂ) (m : ι → ℕ) (ν : κ → ℂ) (q : κ → ℕ)
    (hm_pos : ∀ i, 0 < m i) (hq_pos : ∀ j, 0 < q j)
    (hprofile : ∀ z n, jordanProfile μ m z n = jordanProfile ν q z n)
    (z : ℂ) (s : ℕ) :
    jordanPairCount μ m z s = jordanPairCount ν q z s := by
  by_cases hs : s = 0
  · subst s
    classical
    have hleft : jordanPairCount μ m z 0 = 0 := by
      unfold jordanPairCount
      apply Finset.sum_eq_zero
      intro i _
      have hmi := Nat.ne_of_gt (hm_pos i)
      simp [hmi]
    have hright : jordanPairCount ν q z 0 = 0 := by
      unfold jordanPairCount
      apply Finset.sum_eq_zero
      intro j _
      have hqj := Nat.ne_of_gt (hq_pos j)
      simp [hqj]
    rw [hleft, hright]
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    have hlargePred := jordanLargeCount_eq_of_profile_eq μ m ν q hprofile z (s - 1)
    have hlarge := jordanLargeCount_eq_of_profile_eq μ m ν q hprofile z s
    rw [jordanLargeCount_pred μ m z hspos,
      jordanLargeCount_pred ν q z hspos, hlarge] at hlargePred
    omega

theorem card_pairFiber_eq_jordanPairCount {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (m : ι → ℕ) (z : ℂ) (s : ℕ) :
    Fintype.card {i // (μ i, m i) = (z, s)} = jordanPairCount μ m z s := by
  classical
  let P : Set ι := {i | (μ i, m i) = (z, s)}
  change Fintype.card P = jordanPairCount μ m z s
  rw [← Set.toFinset_card P]
  have hfinset : P.toFinset = Finset.univ.filter fun i => (μ i, m i) = (z, s) := by
    ext i
    simp [P]
  rw [hfinset, Finset.card_filter]
  unfold jordanPairCount
  apply Finset.sum_congr rfl
  intro i _
  simp [Prod.ext_iff]

theorem exists_pairPreservingEquiv_of_profile_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → ℂ) (m : ι → ℕ) (ν : κ → ℂ) (q : κ → ℕ)
    (hm_pos : ∀ i, 0 < m i) (hq_pos : ∀ j, 0 < q j)
    (hprofile : ∀ z n, jordanProfile μ m z n = jordanProfile ν q z n) :
    ∃ e : ι ≃ κ, ∀ i, (ν (e i), q (e i)) = (μ i, m i) := by
  classical
  let leftPair : ι → ℂ × ℕ := fun i => (μ i, m i)
  let rightPair : κ → ℂ × ℕ := fun j => (ν j, q j)
  have hcard : ∀ c : ℂ × ℕ,
      Fintype.card {i // leftPair i = c} = Fintype.card {j // rightPair j = c} := by
    intro c
    rw [show Fintype.card {i // leftPair i = c} = jordanPairCount μ m c.1 c.2 by
      simpa [leftPair] using card_pairFiber_eq_jordanPairCount μ m c.1 c.2]
    rw [show Fintype.card {j // rightPair j = c} = jordanPairCount ν q c.1 c.2 by
      simpa [rightPair] using card_pairFiber_eq_jordanPairCount ν q c.1 c.2]
    exact jordanPairCount_eq_of_profile_eq μ m ν q hm_pos hq_pos hprofile c.1 c.2
  let fiberEquiv : (c : ℂ × ℕ) → {i // leftPair i = c} ≃ {j // rightPair j = c} :=
    fun c => Fintype.equivOfCardEq (hcard c)
  let e : ι ≃ κ := Equiv.ofFiberEquiv fiberEquiv
  refine ⟨e, ?_⟩
  intro i
  change rightPair (e i) = leftPair i
  rw [show e i = (fiberEquiv (leftPair i)) ((Equiv.sigmaFiberEquiv leftPair).symm i).2 by
    exact Equiv.ofFiberEquiv_apply fiberEquiv i]
  exact ((fiberEquiv (leftPair i)) ((Equiv.sigmaFiberEquiv leftPair).symm i).2).2

def localClockEquiv (m : ℕ) (zeta : ℂ) (hzeta : zeta ≠ 0) :
    (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) where
  toFun v j := (zeta⁻¹) ^ (j : ℕ) * v j
  invFun v j := zeta ^ (j : ℕ) * v j
  left_inv v := by
    funext j
    change zeta ^ (j : ℕ) * ((zeta⁻¹) ^ (j : ℕ) * v j) = v j
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hzeta, one_pow, one_mul]
  right_inv v := by
    funext j
    change (zeta⁻¹) ^ (j : ℕ) * (zeta ^ (j : ℕ) * v j) = v j
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hzeta, one_pow, one_mul]
  map_add' v w := by
    funext j
    simp [mul_add]
  map_smul' c v := by
    funext j
    simp
    ring

def jetReindexEquiv {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) :
    ((i : ι) → Fin (m i) → ℂ) ≃ₗ[ℂ] ((i : ι) → Fin (m i) → ℂ) :=
  (LinearEquiv.piCongrRight fun i =>
    LinearEquiv.cast (R := ℂ) (M := fun n : ℕ => Fin n → ℂ)
      (by simpa using hm (e.symm i))).trans
    (LinearEquiv.piCongrLeft ℂ (fun i => Fin (m i) → ℂ) e.symm)

def blockClockEquiv {ι : Type*} (m : ι → ℕ) (zeta : ℂ) (hzeta : zeta ≠ 0) :
    ((i : ι) → Fin (m i) → ℂ) ≃ₗ[ℂ] ((i : ι) → Fin (m i) → ℂ) where
  toFun v i := localClockEquiv (m i) zeta hzeta (v i)
  invFun v i := (localClockEquiv (m i) zeta hzeta).symm (v i)
  left_inv v := by
    funext i
    exact (localClockEquiv (m i) zeta hzeta).left_inv (v i)
  right_inv v := by
    funext i
    exact (localClockEquiv (m i) zeta hzeta).right_inv (v i)
  map_add' v w := by
    funext i
    exact (localClockEquiv (m i) zeta hzeta).map_add (v i) (w i)
  map_smul' c v := by
    funext i
    exact (localClockEquiv (m i) zeta hzeta).map_smul c (v i)

abbrev JetIndex {ι : Type*} (m : ι → ℕ) := (i : ι) × Fin (m i)

def sigmaBlockJordan {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ) :
    Module.End ℂ (JetIndex m → ℂ) where
  toFun v x := localJordan (m x.1) (μ x.1) (fun j => v ⟨x.1, j⟩) x.2
  map_add' v w := by
    funext x
    exact congrFun ((localJordan (m x.1) (μ x.1)).map_add
      (fun j => v ⟨x.1, j⟩) (fun j => w ⟨x.1, j⟩)) x.2
  map_smul' c v := by
    funext x
    exact congrFun
      ((localJordan (m x.1) (μ x.1)).map_smul c (fun j => v ⟨x.1, j⟩)) x.2

@[simp] theorem sigmaBlockJordan_apply {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (v : JetIndex m → ℂ) (i : ι) (j : Fin (m i)) :
    sigmaBlockJordan m μ v ⟨i, j⟩ =
      localJordan (m i) (μ i) (fun q => v ⟨i, q⟩) j := rfl

theorem sigmaBlockJordan_pencil_pow_apply {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (nu : ℂ) (n : ℕ) (v : JetIndex m → ℂ) (i : ι) (j : Fin (m i)) :
    ((sigmaBlockJordan m μ - nu • 1) ^ n) v ⟨i, j⟩ =
      ((localJordan (m i) (μ i) - nu • 1) ^ n) (fun q => v ⟨i, q⟩) j := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change ((sigmaBlockJordan m μ - nu • 1) ^ n)
          ((sigmaBlockJordan m μ - nu • 1) v) ⟨i, j⟩ =
        ((localJordan (m i) (μ i) - nu • 1) ^ n)
          ((localJordan (m i) (μ i) - nu • 1) (fun q => v ⟨i, q⟩)) j
      rw [ih]
      congr 2

def sigmaBlockJordanKerEquiv {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (nu : ℂ) (n : ℕ) :
    LinearMap.ker ((sigmaBlockJordan m μ - nu • 1) ^ n) ≃ₗ[ℂ]
      ((i : ι) → LinearMap.ker ((localJordan (m i) (μ i) - nu • 1) ^ n)) where
  toFun v i := ⟨fun j => v.1 ⟨i, j⟩, by
    apply LinearMap.mem_ker.mpr
    funext j
    have hv := LinearMap.mem_ker.mp v.2
    have hij := congrFun hv (⟨i, j⟩ : JetIndex m)
    rwa [sigmaBlockJordan_pencil_pow_apply] at hij⟩
  invFun v := ⟨fun x => (v x.1).1 x.2, by
    apply LinearMap.mem_ker.mpr
    funext x
    rw [sigmaBlockJordan_pencil_pow_apply]
    exact congrFun (LinearMap.mem_ker.mp (v x.1).2) x.2⟩
  left_inv v := by
    apply Subtype.ext
    funext x
    rfl
  right_inv v := by
    funext i
    apply Subtype.ext
    funext j
    rfl
  map_add' v w := by
    funext i
    apply Subtype.ext
    funext j
    rfl
  map_smul' c v := by
    funext i
    apply Subtype.ext
    funext j
    rfl

theorem finrank_ker_sigmaBlockJordan_pencil_pow {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (nu : ℂ) (n : ℕ) :
    Module.finrank ℂ (LinearMap.ker ((sigmaBlockJordan m μ - nu • 1) ^ n)) =
      jordanProfile μ m nu n := by
  rw [(sigmaBlockJordanKerEquiv m μ nu n).finrank_eq, Module.finrank_pi_fintype]
  unfold jordanProfile
  apply Finset.sum_congr rfl
  intro i _
  exact finrank_ker_localJordan_sub_pow (m i) n (μ i) nu

def jetIndexEquiv {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) : JetIndex m ≃ JetIndex m :=
  Equiv.sigmaCongr e fun i => Equiv.cast (congrArg Fin (hm i).symm)

@[simp] theorem jetIndexEquiv_apply {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) (i : ι) (j : Fin (m i)) :
    jetIndexEquiv m e hm ⟨i, j⟩ = ⟨e i, Fin.cast (hm i).symm j⟩ := by
  unfold jetIndexEquiv Equiv.sigmaCongr
  rw [Equiv.trans_apply, Equiv.sigmaCongrRight_apply, Equiv.sigmaCongrLeft_apply]
  simp only [Equiv.cast_apply, Fin.cast_eq_cast]

def sigmaJetReindexEquiv {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) :
    (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ) where
  toFun v x := v (jetIndexEquiv m e hm x)
  invFun v x := v ((jetIndexEquiv m e hm).symm x)
  left_inv v := by
    funext x
    simp
  right_inv v := by
    funext x
    simp
  map_add' v w := by
    funext x
    simp
  map_smul' c v := by
    funext x
    simp

def sigmaBlockClockEquiv {ι : Type*} (m : ι → ℕ) (zeta : ℂ) (hzeta : zeta ≠ 0) :
    (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ) where
  toFun v x := (zeta⁻¹) ^ (x.2 : ℕ) * v x
  invFun v x := zeta ^ (x.2 : ℕ) * v x
  left_inv v := by
    funext x
    change zeta ^ (x.2 : ℕ) * ((zeta⁻¹) ^ (x.2 : ℕ) * v x) = v x
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hzeta, one_pow, one_mul]
  right_inv v := by
    funext x
    change (zeta⁻¹) ^ (x.2 : ℕ) * (zeta ^ (x.2 : ℕ) * v x) = v x
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hzeta, one_pow, one_mul]
  map_add' v w := by
    funext x
    simp [mul_add]
  map_smul' c v := by
    funext x
    simp
    ring

def sigmaWeylEquiv {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) (zeta : ℂ) (hzeta : zeta ≠ 0) :
    (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ) :=
  (sigmaJetReindexEquiv m e hm).trans (sigmaBlockClockEquiv m zeta hzeta)

@[simp] theorem sigmaWeylEquiv_apply {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) (zeta : ℂ) (hzeta : zeta ≠ 0)
    (v : JetIndex m → ℂ) (i : ι) (j : Fin (m i)) :
    sigmaWeylEquiv m e hm zeta hzeta v ⟨i, j⟩ =
      (zeta⁻¹) ^ (j : ℕ) * v ⟨e i, Fin.cast (hm i).symm j⟩ := by
  simp [sigmaWeylEquiv, sigmaJetReindexEquiv, sigmaBlockClockEquiv,
    jetIndexEquiv_apply]

theorem sigmaWeylEquiv_intertwine {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (e : ι ≃ ι) (hm : ∀ i, m (e i) = m i)
    (zeta : ℂ) (hzeta : zeta ≠ 0) (hμ : ∀ i, μ (e i) = zeta * μ i)
    (v : JetIndex m → ℂ) :
    sigmaWeylEquiv m e hm zeta hzeta (sigmaBlockJordan m μ v) =
      (zeta • sigmaBlockJordan m μ) (sigmaWeylEquiv m e hm zeta hzeta v) := by
  funext x
  rcases x with ⟨i, j⟩
  change sigmaWeylEquiv m e hm zeta hzeta (sigmaBlockJordan m μ v) ⟨i, j⟩ =
    zeta * sigmaBlockJordan m μ (sigmaWeylEquiv m e hm zeta hzeta v) ⟨i, j⟩
  simp only [sigmaWeylEquiv_apply, sigmaBlockJordan_apply,
    localJordan_apply]
  by_cases hj : (j : ℕ) + 1 < m i
  · have hjs : ((Fin.cast (hm i).symm j : Fin (m (e i))) : ℕ) + 1 < m (e i) := by
      rw [Fin.val_cast, hm i]
      exact hj
    rw [dif_pos hj, dif_pos hjs, hμ]
    have hcastNext :
        (⟨((Fin.cast (hm i).symm j : Fin (m (e i))) : ℕ) + 1, hjs⟩ : Fin (m (e i))) =
          Fin.cast (hm i).symm (⟨(j : ℕ) + 1, hj⟩ : Fin (m i)) := by
      apply Fin.ext
      simp [Fin.val_cast]
    rw [hcastNext]
    rw [pow_succ]
    field_simp
  · have hjs : ¬ ((Fin.cast (hm i).symm j : Fin (m (e i))) : ℕ) + 1 < m (e i) := by
      rw [Fin.val_cast, hm i]
      exact hj
    rw [dif_neg hj, dif_neg hjs, hμ]
    ring

theorem sigmaWeylEquiv_conj {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (e : ι ≃ ι) (hm : ∀ i, m (e i) = m i)
    (zeta : ℂ) (hzeta : zeta ≠ 0) (hμ : ∀ i, μ (e i) = zeta * μ i) :
    (sigmaWeylEquiv m e hm zeta hzeta).conj (sigmaBlockJordan m μ) =
      zeta • sigmaBlockJordan m μ := by
  apply LinearMap.ext
  intro v
  have h := sigmaWeylEquiv_intertwine m μ e hm zeta hzeta hμ
    ((sigmaWeylEquiv m e hm zeta hzeta).symm v)
  simpa [LinearEquiv.conj_apply] using h

def PairRotationInvariant {ι : Type*} (μ : ι → ℂ) (m : ι → ℕ) (zeta : ℂ) : Prop :=
  ∃ e : ι ≃ ι, ∀ i, μ (e i) = zeta * μ i ∧ m (e i) = m i

theorem jordanProfile_scaled_values {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (m : ι → ℕ) {zeta : ℂ} (hzeta : zeta ≠ 0)
    (z : ℂ) (n : ℕ) :
    jordanProfile (fun i => zeta * μ i) m z n = jordanProfile μ m (z / zeta) n := by
  classical
  unfold jordanProfile
  apply Finset.sum_congr rfl
  intro i _
  have hiff : zeta * μ i = z ↔ μ i = z / zeta := by
    constructor
    · intro h
      apply (eq_div_iff hzeta).mpr
      simpa [mul_comm] using h
    · intro h
      rw [h]
      exact mul_div_cancel₀ z hzeta
  simp only [hiff]

theorem kernelProfile_sigmaBlockJordan {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (nu : ℂ) (n : ℕ) :
    kernelProfile (sigmaBlockJordan m μ) nu n = jordanProfile μ m nu n := by
  exact finrank_ker_sigmaBlockJordan_pencil_pow m μ nu n

theorem pairRotationInvariant_of_linearWeyl {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (hm_pos : ∀ i, 0 < m i)
    {zeta : ℂ} (hzeta : zeta ≠ 0)
    (W : (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ))
    (hW : W.conj (sigmaBlockJordan m μ) = zeta • sigmaBlockJordan m μ) :
    PairRotationInvariant μ m zeta := by
  have hprofile : ∀ z n,
      jordanProfile (fun i => zeta * μ i) m z n = jordanProfile μ m z n := by
    intro z n
    rw [jordanProfile_scaled_values μ m hzeta]
    have hrot := kernelProfile_rotation hzeta hW (z / zeta) n
    rw [kernelProfile_sigmaBlockJordan, kernelProfile_sigmaBlockJordan] at hrot
    have hz : zeta * (z / zeta) = z := mul_div_cancel₀ z hzeta
    rw [hz] at hrot
    exact hrot.symm
  obtain ⟨e, he⟩ := exists_pairPreservingEquiv_of_profile_eq
    (fun i => zeta * μ i) m μ m hm_pos hm_pos hprofile
  refine ⟨e, ?_⟩
  intro i
  have hp := he i
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

theorem exists_linearWeyl_of_pairRotationInvariant {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) {zeta : ℂ} (hzeta : zeta ≠ 0)
    (hinv : PairRotationInvariant μ m zeta) :
    ∃ W : (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ),
      W.conj (sigmaBlockJordan m μ) = zeta • sigmaBlockJordan m μ := by
  obtain ⟨e, he⟩ := hinv
  let hm : ∀ i, m (e i) = m i := fun i => (he i).2
  let hμ : ∀ i, μ (e i) = zeta * μ i := fun i => (he i).1
  exact ⟨sigmaWeylEquiv m e hm zeta hzeta,
    sigmaWeylEquiv_conj m μ e hm zeta hzeta hμ⟩

theorem linearWeyl_iff_pairRotationInvariant {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (hm_pos : ∀ i, 0 < m i)
    {zeta : ℂ} (hzeta : zeta ≠ 0) :
    (∃ W : (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ),
      W.conj (sigmaBlockJordan m μ) = zeta • sigmaBlockJordan m μ) ↔
      PairRotationInvariant μ m zeta := by
  constructor
  · rintro ⟨W, hW⟩
    exact pairRotationInvariant_of_linearWeyl m μ hm_pos hzeta W hW
  · exact exists_linearWeyl_of_pairRotationInvariant m μ hzeta

def sigmaCoordinateConjEquiv (I : Type*) :
    (I → ℂ) ≃ₛₗ[starRingEnd ℂ] (I → ℂ) where
  toFun v x := star (v x)
  invFun v x := star (v x)
  left_inv v := by
    funext x
    simp
  right_inv v := by
    funext x
    simp
  map_add' v w := by
    funext x
    simp
  map_smul' c v := by
    funext x
    simp

def sigmaConjugateWeylEquiv {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) (zeta : ℂ) (hzeta : zeta ≠ 0) :
    (JetIndex m → ℂ) ≃ₛₗ[starRingEnd ℂ] (JetIndex m → ℂ) :=
  ((sigmaJetReindexEquiv m e hm).trans (sigmaCoordinateConjEquiv (JetIndex m))).trans
    (sigmaBlockClockEquiv m zeta hzeta)

@[simp] theorem sigmaConjugateWeylEquiv_apply {ι : Type*} (m : ι → ℕ)
    (e : ι ≃ ι) (hm : ∀ i, m (e i) = m i) (zeta : ℂ) (hzeta : zeta ≠ 0)
    (v : JetIndex m → ℂ) (i : ι) (j : Fin (m i)) :
    sigmaConjugateWeylEquiv m e hm zeta hzeta v ⟨i, j⟩ =
      (zeta⁻¹) ^ (j : ℕ) * star (v ⟨e i, Fin.cast (hm i).symm j⟩) := by
  simp [sigmaConjugateWeylEquiv, sigmaJetReindexEquiv, sigmaCoordinateConjEquiv,
    sigmaBlockClockEquiv, jetIndexEquiv_apply]

def PairReflectionRotationInvariant {ι : Type*}
    (μ : ι → ℂ) (m : ι → ℕ) (zeta : ℂ) : Prop :=
  ∃ e : ι ≃ ι, ∀ i, star (μ (e i)) = zeta * μ i ∧ m (e i) = m i

theorem sigmaConjugateWeylEquiv_intertwine {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (e : ι ≃ ι) (hm : ∀ i, m (e i) = m i)
    (zeta : ℂ) (hzeta : zeta ≠ 0) (hμ : ∀ i, star (μ (e i)) = zeta * μ i)
    (v : JetIndex m → ℂ) :
    sigmaConjugateWeylEquiv m e hm zeta hzeta (sigmaBlockJordan m μ v) =
      (zeta • sigmaBlockJordan m μ)
        (sigmaConjugateWeylEquiv m e hm zeta hzeta v) := by
  funext x
  rcases x with ⟨i, j⟩
  change sigmaConjugateWeylEquiv m e hm zeta hzeta
      (sigmaBlockJordan m μ v) ⟨i, j⟩ =
    zeta * sigmaBlockJordan m μ
      (sigmaConjugateWeylEquiv m e hm zeta hzeta v) ⟨i, j⟩
  simp only [sigmaConjugateWeylEquiv_apply, sigmaBlockJordan_apply,
    localJordan_apply]
  by_cases hj : (j : ℕ) + 1 < m i
  · have hjs : ((Fin.cast (hm i).symm j : Fin (m (e i))) : ℕ) + 1 < m (e i) := by
      rw [Fin.val_cast, hm i]
      exact hj
    rw [dif_pos hj, dif_pos hjs]
    rw [star_add, star_mul, hμ]
    have hcastNext :
        (⟨((Fin.cast (hm i).symm j : Fin (m (e i))) : ℕ) + 1, hjs⟩ : Fin (m (e i))) =
          Fin.cast (hm i).symm (⟨(j : ℕ) + 1, hj⟩ : Fin (m i)) := by
      apply Fin.ext
      simp [Fin.val_cast]
    rw [hcastNext, pow_succ]
    field_simp
  · have hjs : ¬ ((Fin.cast (hm i).symm j : Fin (m (e i))) : ℕ) + 1 < m (e i) := by
      rw [Fin.val_cast, hm i]
      exact hj
    rw [dif_neg hj, dif_neg hjs]
    rw [add_zero, star_mul, hμ]
    ring

def ConjugateLinearWeylExists {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (zeta : ℂ) : Prop :=
  ∃ W : (JetIndex m → ℂ) ≃ₛₗ[starRingEnd ℂ] (JetIndex m → ℂ),
    ∀ v, W (sigmaBlockJordan m μ v) =
      (zeta • sigmaBlockJordan m μ) (W v)

theorem exists_conjugateLinearWeyl_of_pairReflectionRotationInvariant
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (μ : ι → ℂ)
    {zeta : ℂ} (hzeta : zeta ≠ 0)
    (hinv : PairReflectionRotationInvariant μ m zeta) :
    ConjugateLinearWeylExists m μ zeta := by
  obtain ⟨e, he⟩ := hinv
  let hm : ∀ i, m (e i) = m i := fun i => (he i).2
  let hμ : ∀ i, star (μ (e i)) = zeta * μ i := fun i => (he i).1
  exact ⟨sigmaConjugateWeylEquiv m e hm zeta hzeta,
    sigmaConjugateWeylEquiv_intertwine m μ e hm zeta hzeta hμ⟩

theorem sigmaCoordinateConjEquiv_intertwine {ι : Type*}
    (m : ι → ℕ) (μ : ι → ℂ) (v : JetIndex m → ℂ) :
    sigmaCoordinateConjEquiv (JetIndex m) (sigmaBlockJordan m μ v) =
      sigmaBlockJordan m (fun i => star (μ i))
        (sigmaCoordinateConjEquiv (JetIndex m) v) := by
  funext x
  rcases x with ⟨i, j⟩
  change star (μ i * v ⟨i, j⟩ +
      if h : (j : ℕ) + 1 < m i then v ⟨i, ⟨(j : ℕ) + 1, h⟩⟩ else 0) =
    star (μ i) * star (v ⟨i, j⟩) +
      if h : (j : ℕ) + 1 < m i then star (v ⟨i, ⟨(j : ℕ) + 1, h⟩⟩) else 0
  by_cases hj : (j : ℕ) + 1 < m i
  · rw [dif_pos hj, star_add, star_mul, dif_pos hj]
    ring
  · rw [dif_neg hj, add_zero, star_mul, dif_neg hj, add_zero]
    ring

theorem pairReflectionRotationInvariant_of_conjugateLinearWeyl
    {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (hm_pos : ∀ i, 0 < m i)
    {zeta : ℂ} (hzeta : zeta ≠ 0)
    (hweyl : ConjugateLinearWeylExists m μ zeta) :
    PairReflectionRotationInvariant μ m zeta := by
  obtain ⟨W, hW⟩ := hweyl
  let C := sigmaCoordinateConjEquiv (JetIndex m)
  let B : (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ) := W.trans C
  have hBintertwine : ∀ v,
      B (sigmaBlockJordan m μ v) =
        ((star zeta) • sigmaBlockJordan m (fun i => star (μ i))) (B v) := by
    intro v
    change C (W (sigmaBlockJordan m μ v)) =
      (star zeta) • sigmaBlockJordan m (fun i => star (μ i)) (C (W v))
    rw [hW v]
    change C (zeta • sigmaBlockJordan m μ (W v)) = _
    rw [C.map_smulₛₗ, sigmaCoordinateConjEquiv_intertwine]
    rfl
  have hBconj : B.conj (sigmaBlockJordan m μ) =
      (star zeta) • sigmaBlockJordan m (fun i => star (μ i)) := by
    apply LinearMap.ext
    intro v
    have h := hBintertwine (B.symm v)
    simpa [LinearEquiv.conj_apply] using h
  have hstarzeta : star zeta ≠ 0 := by
    intro h
    apply hzeta
    have hstar := congrArg star h
    simpa using hstar
  have hprofile : ∀ z n,
      jordanProfile (fun i => star zeta * star (μ i)) m z n =
        jordanProfile μ m z n := by
    intro z n
    rw [jordanProfile_scaled_values (fun i => star (μ i)) m hstarzeta]
    have hconj := kernelProfile_conj B (sigmaBlockJordan m μ) z n
    rw [hBconj, kernelProfile_smul hstarzeta,
      kernelProfile_sigmaBlockJordan, kernelProfile_sigmaBlockJordan] at hconj
    exact hconj
  obtain ⟨e, he⟩ := exists_pairPreservingEquiv_of_profile_eq
    (fun i => star zeta * star (μ i)) m μ m hm_pos hm_pos hprofile
  refine ⟨e, ?_⟩
  intro i
  have hfirst := congrArg Prod.fst (he i)
  have hsecond := congrArg Prod.snd (he i)
  refine ⟨?_, hsecond⟩
  have hstar := congrArg star hfirst
  simpa [map_mul] using hstar

theorem conjugateLinearWeyl_iff_pairReflectionRotationInvariant
    {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (hm_pos : ∀ i, 0 < m i)
    {zeta : ℂ} (hzeta : zeta ≠ 0) :
    ConjugateLinearWeylExists m μ zeta ↔
      PairReflectionRotationInvariant μ m zeta := by
  constructor
  · exact pairReflectionRotationInvariant_of_conjugateLinearWeyl m μ hm_pos hzeta
  · exact exists_conjugateLinearWeyl_of_pairReflectionRotationInvariant m μ hzeta

abbrev TruncatedJet (m : ℕ) :=
  GaloisForLFunctions.RHTower.ShiftPairLocalIntersectionAlgebra.TruncatedRootAlgebra m

def truncatedJetPowerBasis (m : ℕ) : PowerBasis ℂ (TruncatedJet m) :=
  GaloisForLFunctions.RHTower.ShiftPairLocalIntersectionAlgebra.truncatedRootPowerBasis m

def reverseTruncatedJetBasis (m : ℕ) : Module.Basis (Fin m) ℂ (TruncatedJet m) := by
  let pb := truncatedJetPowerBasis m
  have hdim : pb.dim = m := by
    rw [← pb.finrank]
    exact GaloisForLFunctions.RHTower.ShiftPairLocalIntersectionAlgebra.finrank_truncatedRootAlgebra m
  exact (pb.basis.reindex (finCongr hdim)).reindex Fin.revPerm

def localJetJordanEquiv (m : ℕ) : TruncatedJet m ≃ₗ[ℂ] (Fin m → ℂ) :=
  (reverseTruncatedJetBasis m).equivFun

def truncatedJetRoot (m : ℕ) : TruncatedJet m :=
  AdjoinRoot.root ((Polynomial.X : Polynomial ℂ) ^ m)

def localJetCarrier (m : ℕ) (μ : ℂ) : TruncatedJet m :=
  algebraMap ℂ (TruncatedJet m) μ + truncatedJetRoot m

def localJetMultiplication (m : ℕ) (μ : ℂ) : Module.End ℂ (TruncatedJet m) :=
  LinearMap.mulLeft ℂ (localJetCarrier m μ)

@[simp] theorem localJetJordanEquiv_basis (m : ℕ) (i j : Fin m) :
    localJetJordanEquiv m (reverseTruncatedJetBasis m i) j =
      if i = j then 1 else 0 := by
  exact Module.Basis.equivFun_self (reverseTruncatedJetBasis m) i j

theorem truncatedJetRoot_pow_eq_zero (m : ℕ) :
    (truncatedJetRoot m) ^ m = 0 := by
  simpa [truncatedJetRoot] using
    AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial ℂ) ^ m)

theorem reverseTruncatedJetBasis_eq_pow (m : ℕ) (i : Fin m) :
    reverseTruncatedJetBasis m i =
      (truncatedJetRoot m) ^ (m - 1 - (i : ℕ)) := by
  simp [reverseTruncatedJetBasis, truncatedJetPowerBasis,
    Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, truncatedJetRoot]
  change (AdjoinRoot.root ((Polynomial.X : Polynomial ℂ) ^ m)) ^ (m - ((i : ℕ) + 1)) =
    (AdjoinRoot.root ((Polynomial.X : Polynomial ℂ) ^ m)) ^ (m - 1 - (i : ℕ))
  congr 1
  omega

theorem localJetCarrier_mul_reverseBasis (m : ℕ) (μ : ℂ) (i : Fin m) :
    localJetCarrier m μ * reverseTruncatedJetBasis m i =
      μ • reverseTruncatedJetBasis m i +
        if hi : 0 < (i : ℕ) then
          reverseTruncatedJetBasis m ⟨(i : ℕ) - 1, by omega⟩
        else 0 := by
  by_cases hi : 0 < (i : ℕ)
  · rw [dif_pos hi, reverseTruncatedJetBasis_eq_pow,
      reverseTruncatedJetBasis_eq_pow]
    simp only [localJetCarrier, add_mul, Algebra.smul_def]
    congr 1
    rw [← pow_succ']
    congr 1
    omega
  · rw [dif_neg hi, add_zero, reverseTruncatedJetBasis_eq_pow]
    have hi0 : (i : ℕ) = 0 := by omega
    simp only [localJetCarrier, add_mul, Algebra.smul_def]
    rw [show m - 1 - (i : ℕ) = m - 1 by omega]
    rw [← pow_succ']
    rw [show m - 1 + 1 = m by omega, truncatedJetRoot_pow_eq_zero, add_zero]

theorem localJetJordanEquiv_intertwine (m : ℕ) (μ : ℂ) (v : TruncatedJet m) :
    localJetJordanEquiv m (localJetMultiplication m μ v) =
      localJordan m μ (localJetJordanEquiv m v) := by
  let b := reverseTruncatedJetBasis m
  let E := localJetJordanEquiv m
  suffices hmaps : E.toLinearMap.comp (localJetMultiplication m μ) =
      (localJordan m μ).comp E.toLinearMap by
    exact LinearMap.congr_fun hmaps v
  apply b.ext
  intro i
  change E (localJetCarrier m μ * b i) = localJordan m μ (E (b i))
  rw [localJetCarrier_mul_reverseBasis]
  ext j
  by_cases hi : 0 < (i : ℕ)
  · rw [dif_pos hi, map_add, map_smul]
    dsimp only [E, b]
    simp only [Pi.add_apply, Pi.smul_apply, localJetJordanEquiv_basis,
      localJordan_apply]
    change μ * (if i = j then 1 else 0) +
        (if (⟨(i : ℕ) - 1, by omega⟩ : Fin m) = j then 1 else 0) =
      μ * (if i = j then 1 else 0) +
        if h : (j : ℕ) + 1 < m then
          if i = (⟨(j : ℕ) + 1, h⟩ : Fin m) then 1 else 0
        else 0
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  · rw [dif_neg hi, add_zero, map_smul]
    dsimp only [E, b]
    simp only [Pi.smul_apply, localJetJordanEquiv_basis, localJordan_apply]
    change μ * (if i = j then 1 else 0) =
      μ * (if i = j then 1 else 0) +
        if h : (j : ℕ) + 1 < m then
          if i = (⟨(j : ℕ) + 1, h⟩ : Fin m) then 1 else 0
        else 0
    split_ifs <;> simp_all [Fin.ext_iff]

def localJetScaleAlgHom (m : ℕ) (zeta : ℂ) :
    TruncatedJet m →ₐ[ℂ] TruncatedJet m := by
  let x := truncatedJetRoot m
  have hroot : Polynomial.eval₂ (algebraMap ℂ (TruncatedJet m))
      (zeta • x) ((Polynomial.X : Polynomial ℂ) ^ m) = 0 := by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [smul_pow, truncatedJetRoot_pow_eq_zero, smul_zero]
  let f := AdjoinRoot.lift (algebraMap ℂ (TruncatedJet m)) (zeta • x) hroot
  exact
    { f with
      commutes' := fun c => by
        change f (AdjoinRoot.of ((Polynomial.X : Polynomial ℂ) ^ m) c) = _
        rw [AdjoinRoot.lift_of hroot] }

@[simp] theorem localJetScaleAlgHom_root (m : ℕ) (zeta : ℂ) :
    localJetScaleAlgHom m zeta (truncatedJetRoot m) =
      zeta • truncatedJetRoot m := by
  simp [localJetScaleAlgHom, truncatedJetRoot, AdjoinRoot.lift_root]

def localJetScaleAlgEquiv (m : ℕ) (zeta : ℂ) (hzeta : zeta ≠ 0) :
    TruncatedJet m ≃ₐ[ℂ] TruncatedJet m := by
  let f := localJetScaleAlgHom m zeta
  let g := localJetScaleAlgHom m zeta⁻¹
  apply AlgEquiv.ofAlgHom f g
  · apply AdjoinRoot.algHom_ext
    change localJetScaleAlgHom m zeta
        (localJetScaleAlgHom m zeta⁻¹ (truncatedJetRoot m)) = truncatedJetRoot m
    rw [localJetScaleAlgHom_root, map_smul, localJetScaleAlgHom_root, smul_smul,
      inv_mul_cancel₀ hzeta, one_smul]
  · apply AdjoinRoot.algHom_ext
    change localJetScaleAlgHom m zeta⁻¹
        (localJetScaleAlgHom m zeta (truncatedJetRoot m)) = truncatedJetRoot m
    rw [localJetScaleAlgHom_root, map_smul, localJetScaleAlgHom_root, smul_smul,
      mul_inv_cancel₀ hzeta, one_smul]

@[simp] theorem localJetScaleAlgEquiv_root (m : ℕ) (zeta : ℂ) (hzeta : zeta ≠ 0) :
    localJetScaleAlgEquiv m zeta hzeta (truncatedJetRoot m) =
      zeta • truncatedJetRoot m := by
  simp [localJetScaleAlgEquiv]

abbrev WindowJetAlgebra {ι : Type*} (m : ι → ℕ) :=
  (i : ι) → TruncatedJet (m i)

def windowJetCarrier {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ) :
    WindowJetAlgebra m :=
  fun i => localJetCarrier (m i) (μ i)

def windowJetMultiplication {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ) :
    Module.End ℂ (WindowJetAlgebra m) :=
  LinearMap.mulLeft ℂ (windowJetCarrier m μ)

def piSigmaLinearEquiv {ι : Type*} (m : ι → ℕ) :
    ((i : ι) → Fin (m i) → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ) where
  toFun v x := v x.1 x.2
  invFun v i j := v ⟨i, j⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def windowJetJordanEquiv {ι : Type*} (m : ι → ℕ) :
    WindowJetAlgebra m ≃ₗ[ℂ] (JetIndex m → ℂ) :=
  (LinearEquiv.piCongrRight fun i => localJetJordanEquiv (m i)).trans
    (piSigmaLinearEquiv m)

@[simp] theorem windowJetJordanEquiv_apply {ι : Type*} (m : ι → ℕ)
    (v : WindowJetAlgebra m) (i : ι) (j : Fin (m i)) :
    windowJetJordanEquiv m v ⟨i, j⟩ = localJetJordanEquiv (m i) (v i) j := rfl

theorem windowJetJordanEquiv_intertwine {ι : Type*}
    (m : ι → ℕ) (μ : ι → ℂ) (v : WindowJetAlgebra m) :
    windowJetJordanEquiv m (windowJetMultiplication m μ v) =
      sigmaBlockJordan m μ (windowJetJordanEquiv m v) := by
  funext x
  rcases x with ⟨i, j⟩
  change localJetJordanEquiv (m i)
      (localJetCarrier (m i) (μ i) * v i) j =
    localJordan (m i) (μ i) (localJetJordanEquiv (m i) (v i)) j
  exact congrFun (localJetJordanEquiv_intertwine (m i) (μ i) (v i)) j

theorem windowJetJordanEquiv_conj {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ) :
    (windowJetJordanEquiv m).conj (windowJetMultiplication m μ) =
      sigmaBlockJordan m μ := by
  apply LinearMap.ext
  intro v
  have h := windowJetJordanEquiv_intertwine m μ ((windowJetJordanEquiv m).symm v)
  simpa [LinearEquiv.conj_apply] using h

@[simp] theorem cast_truncatedJetRoot {a b : ℕ} (h : a = b) :
    AlgEquiv.cast (R := ℂ) (A := TruncatedJet) h (truncatedJetRoot a) =
      truncatedJetRoot b := by
  subst b
  rfl

def windowJetReindexAlgEquiv {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) :
    WindowJetAlgebra m ≃ₐ[ℂ] WindowJetAlgebra m :=
  (AlgEquiv.piCongrRight fun i =>
    AlgEquiv.cast (R := ℂ) (A := TruncatedJet)
      (by simpa using hm (e.symm i))).trans
    (AlgEquiv.piCongrLeft ℂ (fun i => TruncatedJet (m i)) e.symm)

def windowJetAlgEquiv {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) (zeta : ℂ) (hzeta : zeta ≠ 0) :
    WindowJetAlgebra m ≃ₐ[ℂ] WindowJetAlgebra m :=
  (windowJetReindexAlgEquiv m e hm).trans
    (AlgEquiv.piCongrRight fun i => localJetScaleAlgEquiv (m i) zeta hzeta)

theorem piCongrLeft_apply_heq {α β : Type*} (P : β → Type*)
    (e : α ≃ β) (f : (a : α) → P (e a)) (b : β) :
    HEq ((Equiv.piCongrLeft P e) f b) (f (e.symm b)) := by
  rw [Equiv.piCongrLeft_apply]
  exact eqRec_heq _ _

@[simp] theorem windowJetAlgEquiv_apply {ι : Type*} (m : ι → ℕ) (e : ι ≃ ι)
    (hm : ∀ i, m (e i) = m i) (zeta : ℂ) (hzeta : zeta ≠ 0)
    (v : WindowJetAlgebra m) (i : ι) :
    windowJetAlgEquiv m e hm zeta hzeta v i =
      localJetScaleAlgEquiv (m i) zeta hzeta
        (AlgEquiv.cast (R := ℂ) (A := TruncatedJet) (hm i) (v (e i))) := by
  simp [windowJetAlgEquiv, windowJetReindexAlgEquiv]
  apply eq_of_heq
  refine (piCongrLeft_apply_heq (fun i => TruncatedJet (m i)) e.symm
    ((AlgEquiv.piCongrRight fun i =>
      AlgEquiv.cast (R := ℂ) (A := TruncatedJet)
        (by simpa using hm (e.symm i))) v) i).trans ?_
  rw [AlgEquiv.piCongrRight_apply]
  refine (cast_heq _ _).trans ?_
  exact (cast_heq _ _).symm

@[simp] theorem cast_localJetCarrier {a b : ℕ} (h : a = b) (μ : ℂ) :
    AlgEquiv.cast (R := ℂ) (A := TruncatedJet) h (localJetCarrier a μ) =
      localJetCarrier b μ := by
  subst b
  rfl

theorem windowJetAlgEquiv_carrier {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ)
    (e : ι ≃ ι) (hm : ∀ i, m (e i) = m i)
    (zeta : ℂ) (hzeta : zeta ≠ 0) (hμ : ∀ i, μ (e i) = zeta * μ i) :
    windowJetAlgEquiv m e hm zeta hzeta (windowJetCarrier m μ) =
      zeta • windowJetCarrier m μ := by
  funext i
  rw [windowJetAlgEquiv_apply]
  change localJetScaleAlgEquiv (m i) zeta hzeta
      (AlgEquiv.cast (R := ℂ) (A := TruncatedJet) (hm i)
        (localJetCarrier (m (e i)) (μ (e i)))) =
    zeta • localJetCarrier (m i) (μ i)
  rw [cast_localJetCarrier, hμ]
  simp only [localJetCarrier]
  rw [show algebraMap ℂ (TruncatedJet (m i)) (zeta * μ i) =
      (zeta * μ i) • (1 : TruncatedJet (m i)) by simp [Algebra.smul_def]]
  rw [show algebraMap ℂ (TruncatedJet (m i)) (μ i) =
      μ i • (1 : TruncatedJet (m i)) by simp [Algebra.smul_def]]
  rw [map_add, map_smul, map_one, localJetScaleAlgEquiv_root]
  simp [smul_add, mul_smul]

theorem windowJetAlgEquiv_conj_multiplication {ι : Type*}
    (m : ι → ℕ) (μ : ι → ℂ)
    (e : ι ≃ ι) (hm : ∀ i, m (e i) = m i)
    (zeta : ℂ) (hzeta : zeta ≠ 0) (hμ : ∀ i, μ (e i) = zeta * μ i) :
    (windowJetAlgEquiv m e hm zeta hzeta).toLinearEquiv.conj
        (windowJetMultiplication m μ) =
      zeta • windowJetMultiplication m μ := by
  let σ := windowJetAlgEquiv m e hm zeta hzeta
  have hcarrier : σ (windowJetCarrier m μ) = zeta • windowJetCarrier m μ :=
    windowJetAlgEquiv_carrier m μ e hm zeta hzeta hμ
  apply LinearMap.ext
  intro v
  change σ (windowJetCarrier m μ * σ.symm v) =
    zeta • (windowJetCarrier m μ * v)
  rw [map_mul, hcarrier]
  simp

def SemilinearAlgebraWeylExists {ι : Type*}
    (m : ι → ℕ) (μ : ι → ℂ) (zeta : ℂ) : Prop :=
  ∃ σ : WindowJetAlgebra m ≃ₐ[ℂ] WindowJetAlgebra m,
    ∃ W : WindowJetAlgebra m ≃ₗ[ℂ] WindowJetAlgebra m,
      (∀ f v, W (f * v) = σ f * W v) ∧
        W.conj (windowJetMultiplication m μ) =
          zeta • windowJetMultiplication m μ

theorem exists_semilinearAlgebraWeyl_of_pairRotationInvariant
    {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) {zeta : ℂ} (hzeta : zeta ≠ 0)
    (hinv : PairRotationInvariant μ m zeta) :
    SemilinearAlgebraWeylExists m μ zeta := by
  obtain ⟨e, he⟩ := hinv
  let hm : ∀ i, m (e i) = m i := fun i => (he i).2
  let hμ : ∀ i, μ (e i) = zeta * μ i := fun i => (he i).1
  let σ := windowJetAlgEquiv m e hm zeta hzeta
  refine ⟨σ, σ.toLinearEquiv, ?_, ?_⟩
  · intro f v
    exact map_mul σ f v
  · exact windowJetAlgEquiv_conj_multiplication m μ e hm zeta hzeta hμ

theorem pairRotationInvariant_of_semilinearAlgebraWeyl
    {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (hm_pos : ∀ i, 0 < m i)
    {zeta : ℂ} (hzeta : zeta ≠ 0)
    (hweyl : SemilinearAlgebraWeylExists m μ zeta) :
    PairRotationInvariant μ m zeta := by
  obtain ⟨_σ, W, _hsemi, hW⟩ := hweyl
  let E := windowJetJordanEquiv m
  let B : (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ) :=
    E.symm.trans (W.trans E)
  have hWintertwine : ∀ v,
      W (windowJetMultiplication m μ v) =
        (zeta • windowJetMultiplication m μ) (W v) := by
    intro v
    have h := LinearMap.congr_fun hW (W v)
    simpa [LinearEquiv.conj_apply] using h
  have hBintertwine : ∀ v,
      B (sigmaBlockJordan m μ v) =
        (zeta • sigmaBlockJordan m μ) (B v) := by
    intro v
    change E (W (E.symm (sigmaBlockJordan m μ v))) =
      zeta • sigmaBlockJordan m μ (E (W (E.symm v)))
    have hEinv : E.symm (sigmaBlockJordan m μ v) =
        windowJetMultiplication m μ (E.symm v) := by
      have h := windowJetJordanEquiv_intertwine m μ (E.symm v)
      rw [E.symm_apply_eq]
      rw [h]
      rw [show windowJetJordanEquiv m (E.symm v) = v by
        exact E.apply_symm_apply v]
    rw [hEinv, hWintertwine]
    change E (zeta • windowJetMultiplication m μ (W (E.symm v))) = _
    rw [map_smul, windowJetJordanEquiv_intertwine]
  have hBconj : B.conj (sigmaBlockJordan m μ) =
      zeta • sigmaBlockJordan m μ := by
    apply LinearMap.ext
    intro v
    have h := hBintertwine (B.symm v)
    simpa [LinearEquiv.conj_apply] using h
  exact pairRotationInvariant_of_linearWeyl m μ hm_pos hzeta B hBconj

theorem semilinearAlgebraWeyl_iff_pairRotationInvariant
    {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (μ : ι → ℂ) (hm_pos : ∀ i, 0 < m i)
    {zeta : ℂ} (hzeta : zeta ≠ 0) :
    SemilinearAlgebraWeylExists m μ zeta ↔ PairRotationInvariant μ m zeta := by
  constructor
  · exact pairRotationInvariant_of_semilinearAlgebraWeyl m μ hm_pos hzeta
  · exact exists_semilinearAlgebraWeyl_of_pairRotationInvariant m μ hzeta

theorem det_conj {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (W : V ≃ₗ[ℂ] V) (T : Module.End ℂ V) :
    LinearMap.det (W.conj T) = LinearMap.det T := by
  have hforwardInverse : W.toLinearMap * W.symm.toLinearMap = 1 := by
    ext v
    simp [Module.End.mul_apply]
  change LinearMap.det (W.toLinearMap * T * W.symm.toLinearMap) = LinearMap.det T
  simp only [map_mul]
  have hdetInverse := congrArg LinearMap.det hforwardInverse
  simp only [map_mul, map_one] at hdetInverse
  calc
    LinearMap.det W.toLinearMap * LinearMap.det T * LinearMap.det W.symm.toLinearMap =
        (LinearMap.det W.toLinearMap * LinearMap.det W.symm.toLinearMap) *
          LinearMap.det T := by ring
    _ = LinearMap.det T := by rw [hdetInverse, one_mul]

theorem primitiveRoot_dvd_finrank_of_conj_smul_of_leftInverse
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} {zeta : ℂ} (hprimitive : IsPrimitiveRoot zeta n)
    {W : V ≃ₗ[ℂ] V} {T L : Module.End ℂ V}
    (hW : W.conj T = zeta • T) (hleft : L * T = 1) :
    n ∣ Module.finrank ℂ V := by
  have hdetT : LinearMap.det T ≠ 0 := by
    intro hzero
    have hdetLeft := congrArg LinearMap.det hleft
    simp only [map_mul, map_one, hzero, mul_zero] at hdetLeft
    exact one_ne_zero hdetLeft.symm
  have hdet := congrArg LinearMap.det hW
  rw [det_conj, LinearMap.det_smul] at hdet
  have hpow : zeta ^ Module.finrank ℂ V = 1 := by
    apply (mul_right_cancel₀ hdetT)
    simpa [mul_comm] using hdet.symm
  exact (hprimitive.pow_eq_one_iff_dvd _).mp hpow

def sigmaBlockJordanLeftInverse {ι : Type*} (m : ι → ℕ) (μ : ι → ℂ) :
    Module.End ℂ (JetIndex m → ℂ) where
  toFun v x := localJordanLeftInverse (m x.1) (μ x.1)
    (fun j => v ⟨x.1, j⟩) x.2
  map_add' v w := by
    funext x
    exact congrFun ((localJordanLeftInverse (m x.1) (μ x.1)).map_add
      (fun j => v ⟨x.1, j⟩) (fun j => w ⟨x.1, j⟩)) x.2
  map_smul' c v := by
    funext x
    exact congrFun ((localJordanLeftInverse (m x.1) (μ x.1)).map_smul c
      (fun j => v ⟨x.1, j⟩)) x.2

theorem sigmaBlockJordanLeftInverse_mul {ι : Type*}
    (m : ι → ℕ) (μ : ι → ℂ) (hμ : ∀ i, μ i ≠ 0) :
    sigmaBlockJordanLeftInverse m μ * sigmaBlockJordan m μ = 1 := by
  apply LinearMap.ext
  intro v
  funext x
  rcases x with ⟨i, j⟩
  change localJordanLeftInverse (m i) (μ i)
      (localJordan (m i) (μ i) (fun q => v ⟨i, q⟩)) j = v ⟨i, j⟩
  have h := LinearMap.congr_fun (localJordanLeftInverse_mul (m i) (hμ i))
    (fun q => v ⟨i, q⟩)
  exact congrFun h j

theorem finrank_jetSpace {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    Module.finrank ℂ (JetIndex m → ℂ) = ∑ i, m i := by
  rw [Module.finrank_pi_fintype]
  simp [JetIndex, Fintype.card_sigma]

theorem primitiveRoot_dvd_totalJetDimension_of_linearWeyl
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (μ : ι → ℂ)
    (hμ : ∀ i, μ i ≠ 0) {n : ℕ} {zeta : ℂ}
    (hprimitive : IsPrimitiveRoot zeta n)
    (hweyl : ∃ W : (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ),
      W.conj (sigmaBlockJordan m μ) = zeta • sigmaBlockJordan m μ) :
    n ∣ ∑ i, m i := by
  obtain ⟨W, hW⟩ := hweyl
  have hdvd := primitiveRoot_dvd_finrank_of_conj_smul_of_leftInverse
    hprimitive hW (sigmaBlockJordanLeftInverse_mul m μ hμ)
  rwa [finrank_jetSpace] at hdvd

theorem primitiveRoot_dvd_totalJetDimension_of_semilinearAlgebraWeyl
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (μ : ι → ℂ)
    (hm_pos : ∀ i, 0 < m i) (hμ : ∀ i, μ i ≠ 0) {n : ℕ} {zeta : ℂ}
    (hprimitive : IsPrimitiveRoot zeta n)
    (hn : n ≠ 0)
    (hweyl : SemilinearAlgebraWeylExists m μ zeta) :
    n ∣ ∑ i, m i := by
  have hzeta : zeta ≠ 0 := hprimitive.ne_zero hn
  have hinv := pairRotationInvariant_of_semilinearAlgebraWeyl
    m μ hm_pos hzeta hweyl
  exact primitiveRoot_dvd_totalJetDimension_of_linearWeyl m μ hμ hprimitive
    (exists_linearWeyl_of_pairRotationInvariant m μ hzeta hinv)

def exponentialJetValue (logp : ℝ) (rho : ℂ) : ℂ :=
  Complex.exp (-(logp : ℂ) * rho)

def exponentialRotationPhase (q a : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * a / q : ℝ) : ℂ) * Complex.I)

def exponentialVerticalTranslate (logp q a : ℝ) (rho : ℂ) : ℂ :=
  rho - (((2 * Real.pi * a / (q * logp) : ℝ) : ℂ) * Complex.I)

theorem exponentialJetValue_verticalTranslate
    {logp q : ℝ} (hlogp : logp ≠ 0) (hq : q ≠ 0) (a : ℝ) (rho : ℂ) :
    exponentialJetValue logp (exponentialVerticalTranslate logp q a rho) =
      exponentialRotationPhase q a * exponentialJetValue logp rho := by
  simp only [exponentialJetValue, exponentialVerticalTranslate, exponentialRotationPhase]
  rw [← Complex.exp_add]
  congr 1
  have hlogpC : (logp : ℂ) ≠ 0 := by exact_mod_cast hlogp
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast
  field_simp [hlogpC, hqC]
  ring

theorem fixedWindowWeylRigidityClassification_unconditional :
    ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (μ : ι → ℂ),
      (∀ i, 0 < m i) → ∀ zeta : ℂ, zeta ≠ 0 →
        (((∃ W : (JetIndex m → ℂ) ≃ₗ[ℂ] (JetIndex m → ℂ),
            W.conj (sigmaBlockJordan m μ) = zeta • sigmaBlockJordan m μ) ↔
              PairRotationInvariant μ m zeta) ∧
          (ConjugateLinearWeylExists m μ zeta ↔
              PairReflectionRotationInvariant μ m zeta) ∧
          (SemilinearAlgebraWeylExists m μ zeta ↔
              PairRotationInvariant μ m zeta)) := by
  intro ι _ m μ hm_pos zeta hzeta
  exact ⟨linearWeyl_iff_pairRotationInvariant m μ hm_pos hzeta,
    conjugateLinearWeyl_iff_pairReflectionRotationInvariant m μ hm_pos hzeta,
    semilinearAlgebraWeyl_iff_pairRotationInvariant m μ hm_pos hzeta⟩

end WindowJetWeylClassification
end RHTower
end GaloisForLFunctions
