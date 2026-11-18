import GaloisForLFunctions.CountingHolography.Sections.AdelicCarryOnSectionRepresentatives
import GaloisForLFunctions.CountingHolography.Sections.PrimeTraceWindows
import GaloisForLFunctions.CountingHolography.Sections.SectionHeightsAndThePickIndex
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.FinitePrimeAvoidance

/-!
# Shared midpoint section encoding on prime-supported displacement planes

This module constructs the unconditional shared midpoint section encoding on
disjoint-prime-support signed displacement planes over the fixed two-atom positive
background `(p, b)` and proves the sharp global promotion equivalences:

1. **Unconditional prime-supported signed displacement planes and subspaces:**
   Combining bounded-ratio integer moment kernels (`positive_integer_window_moments`)
   with short-interval prime supply (`eventually_prime_avoids_small_finset`) produces,
   at every conductor separation factor `R ≥ 2` and above any finite cutoff `P₀`,
   linearly independent zero-sum signed divisors `a₁, a₂ : Fin N → ℤ` supported
   solely on disjoint finite sets of primes in `(M, 2M]` and `(2RM, 4RM]` such that
   every nonzero integral combination `c₁ • a₁ + c₂ • a₂` has `0 < Q(c₁ • a₁ + c₂ • a₂)`.
   The same construction yields rank-`r` prime-supported lattices for every `r ≥ 1`.

2. **Complete shared midpoint solution over the fixed two-atom prime background:**
   Over the fixed positive background `(p, b)` from `exists_prime_background_subquadraticMidpointTest`,
   the single explicit rational-section rule `adelicSectionEncode` / `adelicSectionDecode`
   serves every `(c₁, c₂) ∈ ℤ²` in `ℤ a₁ ⊕ ℤ a₂`, every sufficiently large background
   translation `k`, and all sufficiently large `m` with `maxFibre = 1`
   (`log maxFibre = 0 ≤ ε m²`), paying every ambiguous narrow-slice digit by `ratPrimeVal 3`
   on the wide rational section representative with zero-loss recovery at every modulus
   coprime to `3` and producing `0 ≤ midpointExcess` from arithmetic.

3. **Sharp promotion equivalence and prime-support negative-index law:**
   Promoting subquadratic-fibre midpoint encoding over that **same** fixed background
   `(p, b)` to all disjoint-prime-support signed planes — and already to two-prime
   difference planes (`|supp(a₁)| = |supp(a₂)| = 2`) — is unconditionally equivalent
   to `RiemannHypothesis`. Moreover, prime-supported submatrices of `atomGram` carry
   the full off-line zero index `(rightZeros zetaZeroConfig).encard`.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset Matrix
open ArithmeticScatteringHolography CountingHolography HTGeometry
open HeckeKreinToeplitz RenormalizedIntersectionTheory Zeta23 ExclusionOfTheCriticalState

/-! ### 1. Signed prime-supported divisors and prime-shell moment kernels -/

/-- A divisor `a : Fin N → ℤ` is supported solely on primes (`(i.val + 1).Prime`),
has vanishing total mass (`∑ i, a i = 0`), and carries both strictly positive and
strictly negative entries. -/
def isSignedPrimeSupported {N : ℕ} (a : Fin N → ℤ) : Prop :=
  (∀ i : Fin N, a i ≠ 0 → (i.val + 1).Prime) ∧
  (∑ i : Fin N, a i) = 0 ∧
  (∃ i₁ : Fin N, 0 < a i₁) ∧
  (∃ i₂ : Fin N, a i₂ < 0)

/-- Active conductor set `{i.val + 1 | a i ≠ 0}` of a divisor `a : Fin N → ℤ`. -/
def activeConductors {N : ℕ} (a : Fin N → ℤ) : Finset ℕ :=
  (Finset.univ.filter fun i : Fin N => a i ≠ 0).image fun i => i.val + 1

theorem mem_activeConductors_iff {N : ℕ} (a : Fin N → ℤ) (q : ℕ) :
    q ∈ activeConductors a ↔ ∃ i : Fin N, a i ≠ 0 ∧ i.val + 1 = q := by
  unfold activeConductors
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem activeConductors_subset_primes {N : ℕ} {a : Fin N → ℤ}
    (ha : isSignedPrimeSupported a) {q : ℕ} (hq : q ∈ activeConductors a) : q.Prime := by
  obtain ⟨i, hi, rfl⟩ := (mem_activeConductors_iff a q).mp hq
  exact ha.1 i hi

theorem disjoint_activeConductors_iff {N : ℕ} (a₁ a₂ : Fin N → ℤ) :
    Disjoint (activeConductors a₁) (activeConductors a₂) ↔
      ∀ i : Fin N, a₁ i = 0 ∨ a₂ i = 0 := by
  rw [Finset.disjoint_left]
  constructor
  · intro hd i
    by_contra! hboth
    exact hd ((mem_activeConductors_iff a₁ (i.val + 1)).mpr ⟨i, hboth.1, rfl⟩)
      ((mem_activeConductors_iff a₂ (i.val + 1)).mpr ⟨i, hboth.2, rfl⟩)
  · intro hall q hq₁ hq₂
    obtain ⟨i, hi, hiq⟩ := (mem_activeConductors_iff a₁ q).mp hq₁
    obtain ⟨j, hj, hjq⟩ := (mem_activeConductors_iff a₂ q).mp hq₂
    have hij : i = j := Fin.ext (by omega)
    subst hij
    exact (hall i).elim hi hj

/-- The coordinate embedding `Fin M ↪ Fin N` underlying `padDivisor`. -/
private theorem padEmb_injective {M N : ℕ} (hMN : M ≤ N) :
    Function.Injective (fun i : Fin M => (⟨i.val, i.isLt.trans_le hMN⟩ : Fin N)) :=
  fun _ _ hij => Fin.ext (Fin.mk.inj_iff.mp hij)

/-- Zero-extension keeps every original coordinate. -/
private theorem padDivisor_apply_emb {M N : ℕ} (hMN : M ≤ N) (u : Fin M → ℤ) (i : Fin M) :
    padDivisor hMN u ⟨i.val, i.isLt.trans_le hMN⟩ = u i :=
  (padEmb_injective hMN).extend_apply u 0 i

theorem isSignedPrimeSupported_pad {M N : ℕ} (hMN : M ≤ N) {u : Fin M → ℤ}
    (hu : isSignedPrimeSupported u) :
    isSignedPrimeSupported (padDivisor hMN u) := by
  let e : Fin M → Fin N := fun i => ⟨i.val, i.isLt.trans_le hMN⟩
  have he : Function.Injective e := padEmb_injective hMN
  have hpad (i : Fin M) : padDivisor hMN u (e i) = u i := padDivisor_apply_emb hMN u i
  obtain ⟨hprime, hsum, ⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩⟩ := hu
  refine ⟨?_, ?_, ⟨e i₁, ?_⟩, ⟨e i₂, ?_⟩⟩
  · intro ℓ hℓ
    by_cases hex : ∃ i : Fin M, e i = ℓ
    · obtain ⟨i, rfl⟩ := hex
      rw [hpad] at hℓ
      exact hprime i hℓ
    · exact (hℓ (Function.extend_apply' _ _ _ hex)).elim
  · have hoff : ∀ ℓ : Fin N, ℓ ∉ Finset.univ.image e → padDivisor hMN u ℓ = 0 := by
      intro ℓ hℓ
      exact Function.extend_apply' _ _ _ fun ⟨i, hi⟩ =>
        hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) fun ℓ _ hℓ => hoff ℓ hℓ,
      Finset.sum_image fun i _ j _ h => he h]
    have hcongr : (∑ i : Fin M, padDivisor hMN u (e i)) = ∑ i : Fin M, u i :=
      Finset.sum_congr rfl fun i _ => hpad i
    rw [hcongr, hsum]
  · rw [hpad]; exact hi₁
  · rw [hpad]; exact hi₂

/-- Every dyadic shell `(M, 2M]` eventually contains at least `L` primes. -/
theorem eventually_card_primes_Ioc_ge (L : ℕ) :
    ∀ᶠ M : ℕ in atTop, L ≤ ((Finset.Ioc M (2 * M)).filter Nat.Prime).card := by
  have hev := SurfaceOfSpecZ.ScaleLocality.eventually_prime_avoids_small_finset
    (γ := 0) (β := 2 / 3) (C := L) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev, eventually_ge_atTop 2]
    with M hM hM2
  by_contra! hlt
  let S := (Finset.Ioc M (2 * M)).filter Nat.Prime
  have hcard : (S.card : ℝ) ≤ (L : ℝ) * (M : ℝ) ^ (0 : ℝ) := by
    rw [Real.rpow_zero, mul_one]
    exact_mod_cast hlt.le
  obtain ⟨q, hq_prime, hq_not_mem, hq_gt, hq_le⟩ := hM S hcard
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hrpow_le : (M : ℝ) ^ (2 / 3 : ℝ) ≤ M := by
    calc (M : ℝ) ^ (2 / 3 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
      _ = M := Real.rpow_one M
  have hq_le_2M : q ≤ 2 * M := by
    have : (q : ℝ) ≤ (2 * M : ℕ) := by push_cast; linarith only [hq_le, hrpow_le]
    exact_mod_cast this
  have hq_gt_M : M < q := by exact_mod_cast hq_gt
  exact hq_not_mem (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq_gt_M, hq_le_2M⟩, hq_prime⟩)

private theorem sum_extend_zero {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {e : ι → κ} (he : Function.Injective e) (w : κ → ℝ) (u : ι → ℤ) :
    (∑ ℓ : κ, w ℓ * ((Function.extend e u 0 ℓ : ℤ) : ℝ)) = ∑ i : ι, w (e i) * (u i : ℝ) := by
  have hoff : ∀ ℓ, ℓ ∉ Finset.univ.image e →
      w ℓ * ((Function.extend e u 0 ℓ : ℤ) : ℝ) = 0 := by
    intro ℓ hℓ
    have hz : Function.extend e u 0 ℓ = 0 :=
      Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    rw [hz, Int.cast_zero, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) fun ℓ _ hℓ => hoff ℓ hℓ,
    Finset.sum_image fun i _ j _ h => he h]
  exact Finset.sum_congr rfl fun i _ => by rw [he.extend_apply]

/-- Given `k₀ ≥ 1`, every sufficiently high dyadic shell `(M, 2M]` supports a nonzero
signed prime-supported divisor `u : Fin (2 * M) → ℤ` annihilating the first `k₀`
power moments. -/
theorem exists_primeShell_momentKernel_vector (k₀ : ℕ) (hk₀ : 1 ≤ k₀) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∃ u : Fin (2 * M) → ℤ,
        isSignedPrimeSupported u ∧
        (∀ i : Fin (2 * M), u i ≠ 0 → M < i.val + 1 ∧ i.val + 1 ≤ 2 * M) ∧
        (∀ j < k₀, ∑ i : Fin (2 * M), ((i : ℝ) + 1) ^ j * (u i : ℝ) = 0) := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    ((eventually_card_primes_Ioc_ge (k₀ + 1)).and (eventually_ge_atTop 2))
  refine ⟨max M₀ 2, le_max_right _ _, fun M hM => ?_⟩
  obtain ⟨hcard, hM2⟩ := hM₀ M ((le_max_left M₀ 2).trans hM)
  let S := (Finset.Ioc M (2 * M)).filter Nat.Prime
  let Φ : (↥S → ℚ) →ₗ[ℚ] (Fin k₀ → ℚ) :=
    { toFun := fun v j => ∑ q : ↥S, (q.val : ℚ) ^ j.val * v q
      map_add' := fun v w => funext fun j => by
        change ∑ q : ↥S, (q.val : ℚ) ^ j.val * (v q + w q) = _
        simp only [mul_add, Finset.sum_add_distrib, Pi.add_apply]
      map_smul' := fun c v => funext fun j => by
        change ∑ q : ↥S, (q.val : ℚ) ^ j.val * (c * v q) = c * _
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring }
  have hrank : 0 < Module.finrank ℚ (LinearMap.ker Φ) := by
    have he := Φ.finrank_range_add_finrank_ker
    have hl := Submodule.finrank_le (LinearMap.range Φ)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin] at he hl
    have hc : k₀ + 1 ≤ S.card := hcard
    change 0 < Module.finrank ℚ Φ.ker
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ : ∃ v ∈ LinearMap.ker Φ, v ≠ 0 := by
    by_contra! hall
    have hbot : LinearMap.ker Φ = ⊥ := (Submodule.eq_bot_iff _).mpr hall
    rw [hbot, finrank_bot] at hrank
    exact lt_irrefl 0 hrank
  let D : ℕ := ∏ q : ↥S, (v q).den
  have hD : 0 < D := Finset.prod_pos fun q _ => (v q).den_pos
  let z : ↥S → ℤ := fun q => (v q).num * ((D / (v q).den : ℕ) : ℤ)
  have hz_eq : (fun q : ↥S => (z q : ℚ)) = (D : ℚ) • v := by
    funext q
    obtain ⟨c, hc⟩ : (v q).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ q)
    change (((v q).num * ((D / (v q).den : ℕ) : ℤ) : ℤ) : ℚ) = (D : ℚ) * v q
    rw [hc, Nat.mul_div_cancel_left _ (v q).den_pos]
    have hvd : v q * ((v q).den : ℚ) = ((v q).num : ℚ) := by
      nth_rw 1 [← Rat.num_div_den (v q)]
      exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (v q).den_ne_zero)
    push_cast
    calc ((v q).num : ℚ) * (c : ℚ) = (v q * (v q).den) * (c : ℚ) := by rw [hvd]
      _ = ((v q).den * (c : ℚ)) * v q := by ring
  have hz_ne : z ≠ 0 := by
    intro h0
    apply hv_ne
    funext q
    have hq : (z q : ℚ) = (D : ℚ) * v q := congrFun hz_eq q
    rw [h0, Pi.zero_apply, Int.cast_zero] at hq
    exact (mul_eq_zero.mp hq.symm).resolve_left (Nat.cast_ne_zero.mpr hD.ne')
  have hz_ker : Φ (fun q => (z q : ℚ)) = 0 :=
    LinearMap.mem_ker.mp (hz_eq ▸ (LinearMap.ker Φ).smul_mem _ hv_mem)
  let ι : ↥S → Fin (2 * M) := fun q => ⟨q.val - 1, by
    have hmem := (Finset.mem_filter.mp q.property).1
    have hioc := Finset.mem_Ioc.mp hmem
    omega⟩
  have hι_val (q : ↥S) : (ι q).val + 1 = q.val := by
    dsimp [ι]
    have hioc := Finset.mem_Ioc.mp (Finset.mem_filter.mp q.property).1
    omega
  have hι : Function.Injective ι := by
    intro q₁ q₂ h
    apply Subtype.ext
    have hv₁ := hι_val q₁
    have hv₂ := hι_val q₂
    have heq := congrArg Fin.val h
    omega
  let u : Fin (2 * M) → ℤ := Function.extend ι z 0
  have hu_supp {i : Fin (2 * M)} (hui : u i ≠ 0) :
      (i.val + 1).Prime ∧ M < i.val + 1 ∧ i.val + 1 ≤ 2 * M := by
    by_cases hex : ∃ q : ↥S, ι q = i
    · obtain ⟨q, rfl⟩ := hex
      rw [hι_val q]
      have hmem := Finset.mem_filter.mp q.property
      have hioc := Finset.mem_Ioc.mp hmem.1
      exact ⟨hmem.2, hioc.1, hioc.2⟩
    · exact (hui (Function.extend_apply' _ _ _ hex)).elim
  have hu_mom (j : ℕ) (hj : j < k₀) :
      ∑ i : Fin (2 * M), ((i : ℝ) + 1) ^ j * (u i : ℝ) = 0 := by
    rw [show u = Function.extend ι z 0 from rfl,
      sum_extend_zero hι (fun i : Fin (2 * M) => ((i : ℝ) + 1) ^ j) z]
    have hq_rat := congrFun hz_ker ⟨j, hj⟩
    change ∑ q : ↥S, (q.val : ℚ) ^ j * (z q : ℚ) = 0 at hq_rat
    have hq_real : ∑ q : ↥S, (q.val : ℝ) ^ j * (z q : ℝ) = 0 := by exact_mod_cast hq_rat
    rw [← hq_real]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hvq : ((ι q : ℕ) : ℝ) + 1 = (q.val : ℝ) := by exact_mod_cast hι_val q
    rw [hvq]
  have hu_sum : (∑ i : Fin (2 * M), u i) = 0 := by
    have h0 := hu_mom 0 hk₀
    simp only [pow_zero, one_mul] at h0
    exact_mod_cast h0
  obtain ⟨q₀, hq₀⟩ : ∃ q : ↥S, z q ≠ 0 := by simpa [funext_iff] using hz_ne
  have hui₀ : u (ι q₀) ≠ 0 := by
    simpa only [u, hι.extend_apply] using hq₀
  have hpos_entry : ∃ i₁ : Fin (2 * M), 0 < u i₁ := by
    by_contra! hle
    rcases lt_or_gt_of_ne hui₀ with hneg | hpos
    · have hsplit := Finset.add_sum_erase Finset.univ u (Finset.mem_univ (ι q₀))
      have hrest : ∑ i ∈ Finset.univ.erase (ι q₀), u i ≤ 0 :=
        Finset.sum_nonpos fun i _ => hle i
      linarith only [hsplit, hu_sum, hrest, hneg]
    · exact (hle (ι q₀)).not_gt hpos
  have hneg_entry : ∃ i₂ : Fin (2 * M), u i₂ < 0 := by
    by_contra! hge
    rcases lt_or_gt_of_ne hui₀ with hneg | hpos
    · exact (hge (ι q₀)).not_gt hneg
    · have hsplit := Finset.add_sum_erase Finset.univ u (Finset.mem_univ (ι q₀))
      have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase (ι q₀), u i :=
        Finset.sum_nonneg fun i _ => hge i
      linarith only [hsplit, hu_sum, hrest, hpos]
  exact ⟨u, ⟨fun i hi => (hu_supp hi).1, hu_sum, hpos_entry, hneg_entry⟩,
    fun i hi => ⟨(hu_supp hi).2.1, (hu_supp hi).2.2⟩, hu_mom⟩

/-! ### 2. Unconditional disjoint-prime-support displacement planes and subspaces -/

/-- For every separation ratio `R ≥ 2` and every lower conductor cutoff `P₀`, there
exist a horizon `N > P₀` and two linearly independent signed prime-supported divisors
`a₁, a₂ : Fin N → ℤ` on disjoint prime shells separated by factor `> R` (and above `P₀`)
such that every nonzero integral combination in `ℤ a₁ ⊕ ℤ a₂` has `0 < Q(c₁ • a₁ + c₂ • a₂)`. -/
theorem exists_disjoint_primeSupported_signed_plane (R : ℕ) (hR : 2 ≤ R) (P₀ : ℕ) :
    ∃ (N : ℕ) (a₁ a₂ : Fin N → ℤ),
      P₀ < N ∧
      isSignedPrimeSupported a₁ ∧ isSignedPrimeSupported a₂ ∧
      (∀ i : Fin N, a₁ i ≠ 0 → P₀ < i.val + 1) ∧
      (∀ j : Fin N, a₂ j ≠ 0 → P₀ < j.val + 1) ∧
      (∀ i j : Fin N, a₁ i ≠ 0 → a₂ j ≠ 0 → R * (i.val + 1) < j.val + 1) ∧
      Disjoint (activeConductors a₁) (activeConductors a₂) ∧
      (∀ c₁ c₂ : ℤ, (c₁ • a₁ + c₂ • a₂ = 0 ↔ c₁ = 0 ∧ c₂ = 0)) ∧
      (∀ c₁ c₂ : ℤ, (c₁ ≠ 0 ∨ c₂ ≠ 0) → 0 < integerProbe N (c₁ • a₁ + c₂ • a₂)) := by
  let B := 4 * R
  have hB : 0 < B := by dsimp [B]; omega
  obtain ⟨k, hk_pos⟩ := positive_integer_window_moments B hB
  let k₀ := max k 1
  obtain ⟨M₀, hM₀2, hshell⟩ := exists_primeShell_momentKernel_vector k₀ (le_max_right k 1)
  let M := max M₀ (P₀ + 1)
  have hM_ge : M₀ ≤ M := le_max_left _ _
  have hM_gt_P : P₀ < M := Nat.lt_of_lt_of_le (Nat.lt_succ_self P₀) (le_max_right _ _)
  have h2RM_ge : M₀ ≤ 2 * R * M := by
    have : 1 * M ≤ 2 * R * M := Nat.mul_le_mul_right M (by omega)
    omega
  obtain ⟨u₁, hu₁_sig, hu₁_shell, hu₁_mom⟩ := hshell M hM_ge
  obtain ⟨a₂, ha₂_sig, ha₂_shell, ha₂_mom⟩ := hshell (2 * R * M) h2RM_ge
  let N := 2 * (2 * R * M)
  have h2M_le_N : 2 * M ≤ N := by dsimp [N]; nlinarith only [hR]
  let a₁ : Fin N → ℤ := padDivisor h2M_le_N u₁
  have hN_gt : P₀ < N := by dsimp [N]; nlinarith only [hR, hM_gt_P]
  have ha₁_sig : isSignedPrimeSupported a₁ := isSignedPrimeSupported_pad h2M_le_N hu₁_sig
  let ePad : Fin (2 * M) → Fin N := fun i => ⟨i.val, i.isLt.trans_le h2M_le_N⟩
  have hePad : Function.Injective ePad := padEmb_injective h2M_le_N
  have ha₁_shell {ℓ : Fin N} (hℓ : a₁ ℓ ≠ 0) : M < ℓ.val + 1 ∧ ℓ.val + 1 ≤ 2 * M := by
    by_cases hex : ∃ i : Fin (2 * M), ePad i = ℓ
    · obtain ⟨i, rfl⟩ := hex
      have hui : u₁ i ≠ 0 := by
        rwa [show a₁ (ePad i) = u₁ i from padDivisor_apply_emb h2M_le_N u₁ i] at hℓ
      exact hu₁_shell i hui
    · exact (hℓ (Function.extend_apply' _ _ _ hex)).elim
  have ha₁_mom (j : ℕ) (hj : j < k₀) :
      ∑ ℓ : Fin N, ((ℓ : ℝ) + 1) ^ j * (a₁ ℓ : ℝ) = 0 := by
    rw [show a₁ = Function.extend ePad u₁ 0 from rfl,
      sum_extend_zero hePad (fun ℓ : Fin N => ((ℓ : ℝ) + 1) ^ j) u₁]
    exact hu₁_mom j hj
  have hsep (i j : Fin N) (hi : a₁ i ≠ 0) (hj : a₂ j ≠ 0) :
      R * (i.val + 1) < j.val + 1 := by
    have hi_hi := (ha₁_shell hi).2
    have hj_lo := (ha₂_shell j hj).1
    calc R * (i.val + 1) ≤ R * (2 * M) := Nat.mul_le_mul_left R hi_hi
      _ = 2 * R * M := by ring
      _ < j.val + 1 := hj_lo
  have hdisj_pt (ℓ : Fin N) : a₁ ℓ = 0 ∨ a₂ ℓ = 0 := by
    by_contra! hboth
    have hlt := hsep ℓ ℓ hboth.1 hboth.2
    nlinarith only [hR, hlt]
  have hdisj : Disjoint (activeConductors a₁) (activeConductors a₂) :=
    (disjoint_activeConductors_iff a₁ a₂).mpr hdisj_pt
  obtain ⟨ℓ₁, hℓ₁⟩ := ha₁_sig.2.2.1
  obtain ⟨ℓ₂, hℓ₂⟩ := ha₂_sig.2.2.1
  have hlin (c₁ c₂ : ℤ) : c₁ • a₁ + c₂ • a₂ = 0 ↔ c₁ = 0 ∧ c₂ = 0 := by
    constructor
    · intro h0
      have hv₁ := congrFun h0 ℓ₁
      have hv₂ := congrFun h0 ℓ₂
      have ha₂_0 : a₂ ℓ₁ = 0 := (hdisj_pt ℓ₁).resolve_left hℓ₁.ne'
      have ha₁_0 : a₁ ℓ₂ = 0 := (hdisj_pt ℓ₂).resolve_right hℓ₂.ne'
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hv₁ hv₂
      simp only [zsmul_eq_mul, Int.cast_id, ha₂_0, ha₁_0, mul_zero, add_zero, zero_add] at hv₁ hv₂
      exact ⟨(mul_eq_zero.mp hv₁).resolve_right hℓ₁.ne',
             (mul_eq_zero.mp hv₂).resolve_right hℓ₂.ne'⟩
    · rintro ⟨rfl, rfl⟩; simp
  have hpos_plane (c₁ c₂ : ℤ) (hc : c₁ ≠ 0 ∨ c₂ ≠ 0) :
      0 < integerProbe N (c₁ • a₁ + c₂ • a₂) := by
    have hne : c₁ • a₁ + c₂ • a₂ ≠ 0 := by
      intro h0
      obtain ⟨rfl, rfl⟩ := (hlin c₁ c₂).mp h0
      exact hc.elim (fun h => h rfl) (fun h => h rfl)
    refine hk_pos N (c₁ • a₁ + c₂ • a₂) hne ?_ ?_
    · intro ℓ hℓ
      have hdiv : N / B = M := by
        dsimp [N, B]
        rw [show 2 * (2 * R * M) = (4 * R) * M by ring]
        exact Nat.mul_div_cancel_left M hB
      rw [hdiv] at hℓ
      have h10 : a₁ ℓ = 0 := by by_contra h1; have := (ha₁_shell h1).1; omega
      have h20 : a₂ ℓ = 0 := by
        by_contra h2
        have := (ha₂_shell ℓ h2).1
        have : 1 * M ≤ 2 * R * M := Nat.mul_le_mul_right M (by omega)
        omega
      simp [h10, h20]
    · intro j hj
      have hj' : j < k₀ := hj.trans_le (le_max_left k 1)
      have hexp : (∑ ℓ : Fin N, ((ℓ : ℝ) + 1) ^ j * (((c₁ • a₁ + c₂ • a₂) ℓ : ℤ) : ℝ)) =
          (c₁ : ℝ) * (∑ ℓ : Fin N, ((ℓ : ℝ) + 1) ^ j * (a₁ ℓ : ℝ)) +
            (c₂ : ℝ) * (∑ ℓ : Fin N, ((ℓ : ℝ) + 1) ^ j * (a₂ ℓ : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        change ((ℓ : ℝ) + 1) ^ j * ((c₁ • a₁ ℓ + c₂ • a₂ ℓ : ℤ) : ℝ) = _
        simp only [zsmul_eq_mul]; push_cast; ring
      rw [hexp, ha₁_mom j hj', ha₂_mom j hj', mul_zero, mul_zero, add_zero]
  refine ⟨N, a₁, a₂, hN_gt, ha₁_sig, ha₂_sig, ?_, ?_, hsep, hdisj, hlin, hpos_plane⟩
  · intro i hi; have := (ha₁_shell hi).1; omega
  · intro j hj
    have := (ha₂_shell j hj).1
    have : 1 * M ≤ 2 * R * M := Nat.mul_le_mul_right M (by omega)
    omega

/-- Arbitrary finite-rank generalization: for every rank `r ≥ 1` and lower cutoff `P₀`,
there exist `N > P₀` and `r` pairwise-disjoint signed prime-supported divisors
`a : Fin r → (Fin N → ℤ)` whose `ℤ`-span has strictly positive `integerProbe` on
every nonzero integral combination. -/
theorem exists_disjoint_primeSupported_signed_subspace (r : ℕ) (hr : 1 ≤ r) (P₀ : ℕ) :
    ∃ (N : ℕ) (a : Fin r → (Fin N → ℤ)),
      P₀ < N ∧
      (∀ s : Fin r, isSignedPrimeSupported (a s)) ∧
      (∀ (s : Fin r) (i : Fin N), a s i ≠ 0 → P₀ < i.val + 1) ∧
      (∀ s₁ s₂ : Fin r, s₁ ≠ s₂ → Disjoint (activeConductors (a s₁)) (activeConductors (a s₂))) ∧
      (∀ c : Fin r → ℤ, ((∑ s, c s • a s) = 0 ↔ c = 0)) ∧
      (∀ c : Fin r → ℤ, c ≠ 0 → 0 < integerProbe N (∑ s, c s • a s)) := by
  let B := 2 ^ r
  have hB : 0 < B := pow_pos (by decide) r
  obtain ⟨k, hk_pos⟩ := positive_integer_window_moments B hB
  let k₀ := max k 1
  obtain ⟨M₀, _, hshell⟩ := exists_primeShell_momentKernel_vector k₀ (le_max_right k 1)
  let M := max M₀ (P₀ + 1)
  have hM_gt_P : P₀ < M := Nat.lt_of_lt_of_le (Nat.lt_succ_self P₀) (le_max_right _ _)
  let N := 2 ^ r * M
  have hN_gt : P₀ < N := by
    have : 1 * M ≤ 2 ^ r * M := Nat.mul_le_mul_right M hB
    omega
  have hshell_s (s : Fin r) :
      ∃ a_s : Fin N → ℤ,
        isSignedPrimeSupported a_s ∧
        (∀ ℓ : Fin N, a_s ℓ ≠ 0 → 2 ^ s.val * M < ℓ.val + 1 ∧ ℓ.val + 1 ≤ 2 ^ (s.val + 1) * M) ∧
        (∀ j < k₀, ∑ ℓ : Fin N, ((ℓ : ℝ) + 1) ^ j * (a_s ℓ : ℝ) = 0) := by
    have hs_ge : M₀ ≤ 2 ^ s.val * M := by
      have h1 : 1 * M ≤ 2 ^ s.val * M := Nat.mul_le_mul_right M Nat.one_le_two_pow
      have h2 : M₀ ≤ M := le_max_left _ _
      omega
    obtain ⟨u, hu_sig, hu_sh, hu_mom⟩ := hshell (2 ^ s.val * M) hs_ge
    have hle_N : 2 * (2 ^ s.val * M) ≤ N := by
      rw [show 2 * (2 ^ s.val * M) = 2 ^ (s.val + 1) * M by rw [pow_succ', mul_assoc]]
      exact Nat.mul_le_mul_right M (pow_le_pow_right₀ (by decide : 1 ≤ 2) (by have := s.isLt; omega))
    let a_s : Fin N → ℤ := padDivisor hle_N u
    let e : Fin (2 * (2 ^ s.val * M)) → Fin N := fun i => ⟨i.val, i.isLt.trans_le hle_N⟩
    have he : Function.Injective e := padEmb_injective hle_N
    refine ⟨a_s, isSignedPrimeSupported_pad hle_N hu_sig, ?_, ?_⟩
    · intro ℓ hℓ
      by_cases hex : ∃ i, e i = ℓ
      · obtain ⟨i, rfl⟩ := hex
        have hui : u i ≠ 0 := by
          rwa [show a_s (e i) = u i from padDivisor_apply_emb hle_N u i] at hℓ
        obtain ⟨hlo, hhi⟩ := hu_sh i hui
        exact ⟨hlo, by simpa only [pow_succ', mul_assoc] using hhi⟩
      · exact (hℓ (Function.extend_apply' _ _ _ hex)).elim
    · intro j hj
      rw [show a_s = Function.extend e u 0 from rfl,
        sum_extend_zero he (fun ℓ : Fin N => ((ℓ : ℝ) + 1) ^ j) u]
      exact hu_mom j hj
  choose a ha_sig ha_sh ha_mom using hshell_s
  have hdisj_pt {s₁ s₂ : Fin r} (hne : s₁ ≠ s₂) (ℓ : Fin N) :
      a s₁ ℓ = 0 ∨ a s₂ ℓ = 0 := by
    by_contra! hboth
    have b₁ := ha_sh s₁ ℓ hboth.1
    have b₂ := ha_sh s₂ ℓ hboth.2
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have hpow : 2 ^ (s₁.val + 1) * M ≤ 2 ^ s₂.val * M :=
        Nat.mul_le_mul_right M (pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega))
      omega
    · have hpow : 2 ^ (s₂.val + 1) * M ≤ 2 ^ s₁.val * M :=
        Nat.mul_le_mul_right M (pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega))
      omega
  have hlin (c : Fin r → ℤ) : (∑ s, c s • a s) = 0 ↔ c = 0 := by
    constructor
    · intro h0
      funext s₀
      obtain ⟨ℓ₀, hℓ₀⟩ := (ha_sig s₀).2.2.1
      have hv := congrFun h0 ℓ₀
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at hv
      simp only [zsmul_eq_mul, Int.cast_id] at hv
      rw [Finset.sum_eq_single s₀] at hv
      · exact (mul_eq_zero.mp hv).resolve_right hℓ₀.ne'
      · intro s _ hs
        have h0s : a s ℓ₀ = 0 := (hdisj_pt hs ℓ₀).resolve_right hℓ₀.ne'
        rw [h0s, mul_zero]
      · exact fun h => (h (Finset.mem_univ s₀)).elim
    · rintro rfl; simp
  have hpos_sub (c : Fin r → ℤ) (hc : c ≠ 0) :
      0 < integerProbe N (∑ s, c s • a s) := by
    have hne : (∑ s, c s • a s) ≠ 0 := mt (hlin c).mp hc
    refine hk_pos N (∑ s, c s • a s) hne ?_ ?_
    · intro ℓ hℓ
      have hdiv : N / B = M := Nat.mul_div_cancel_left M hB
      rw [hdiv] at hℓ
      simp only [Finset.sum_apply, Pi.smul_apply]
      simp only [zsmul_eq_mul, Int.cast_id]
      refine Finset.sum_eq_zero fun s _ => ?_
      have h0s : a s ℓ = 0 := by
        by_contra hs_ne
        have hlo := (ha_sh s ℓ hs_ne).1
        have h1 : 1 * M ≤ 2 ^ s.val * M := Nat.mul_le_mul_right M Nat.one_le_two_pow
        omega
      rw [h0s, mul_zero]
    · intro j hj
      have hj' : j < k₀ := hj.trans_le (le_max_left k 1)
      have hexp : (∑ ℓ : Fin N, ((ℓ : ℝ) + 1) ^ j * (((∑ s, c s • a s) ℓ : ℤ) : ℝ)) =
          ∑ s : Fin r, (c s : ℝ) * (∑ ℓ : Fin N, ((ℓ : ℝ) + 1) ^ j * (a s ℓ : ℝ)) := by
        simp_rw [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id, Int.cast_sum, Int.cast_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun ℓ _ => by ring
      rw [hexp]
      exact Finset.sum_eq_zero fun s _ => by rw [ha_mom s j hj', mul_zero]
  refine ⟨N, a, hN_gt, ha_sig, ?_, ?_, hlin, hpos_sub⟩
  · intro s i hi
    have hlo := (ha_sh s i hi).1
    have h1 : 1 * M ≤ 2 ^ s.val * M := Nat.mul_le_mul_right M Nat.one_le_two_pow
    omega
  · intro s₁ s₂ hne
    exact (disjoint_activeConductors_iff _ _).mpr (hdisj_pt hne)

/-! ### 3. Complete shared midpoint solution over the fixed two-atom prime background -/

/-- Complete unconditional shared midpoint encoding on disjoint-prime-support signed
displacement planes over the fixed two-atom positive background `(p, b)` from
`exists_prime_background_subquadraticMidpointTest`. A single explicit rational-section
encoder/decoder pair (`adelicSectionEncode` / `adelicSectionDecode`), defined before
any cardinality comparison, serves every integral combination in `ℤ a₁ ⊕ ℤ a₂`, every
sufficiently large background translation `k`, and all sufficiently large `m` with
`maxFibre = 1` (`log maxFibre ≤ ε m²`), pays every ambiguous carry digit by the
`3`-adic rational valuation `ratPrimeVal 3`, recovers all coprime moduli with zero
loss, and produces the signed second-difference inequality `0 ≤ midpointExcess` from arithmetic. -/
theorem exists_prime_background_shared_adelicCarry_plane :
    ∃ (p : ℕ) (b : Fin (p + 1) → ℤ),
      p.Prime ∧ (b = primePair p ∨ b = primeDifference p) ∧
      0 < integerProbe (p + 1) b ∧
      (RiemannHypothesis ↔ subquadraticMidpointTest b) ∧
      (RiemannHypothesis ↔ adelicMidpointTest b) ∧
      ∀ R : ℕ, 2 ≤ R →
        ∃ (N : ℕ) (hPN : p + 1 ≤ N) (a₁ a₂ : Fin N → ℤ),
          let b_pad := padDivisor hPN b
          isSignedPrimeSupported a₁ ∧ isSignedPrimeSupported a₂ ∧
          Disjoint (activeConductors a₁) (activeConductors a₂) ∧
          Disjoint (activeConductors b_pad) (activeConductors a₁ ∪ activeConductors a₂) ∧
          (∀ i j : Fin N, a₁ i ≠ 0 → a₂ j ≠ 0 → R * (i.val + 1) < j.val + 1) ∧
          (∀ c₁ c₂ : ℤ, (c₁ • a₁ + c₂ • a₂ = 0 ↔ c₁ = 0 ∧ c₂ = 0)) ∧
          ∀ c₁ c₂ : ℤ,
            let a := c₁ • a₁ + c₂ • a₂
            0 ≤ integerProbe N a ∧
            ((c₁ ≠ 0 ∨ c₂ ≠ 0) → 0 < integerProbe N a) ∧
            ∀ᶠ k : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
              let v₀ := m • (k • b_pad)
              let v₁ := m • (k • b_pad + a)
              let v₂ := m • (k • b_pad - a)
              ∃ h : mapsRationalSections (adelicSectionEncode v₀ v₁ v₂) v₀ v₁ v₂,
                maxFibre (restrictRationalSectionMap (adelicSectionEncode v₀ v₁ v₂) h) = 1 ∧
                (∀ ε : ℝ, 0 < ε →
                  Real.log (maxFibre (restrictRationalSectionMap (adelicSectionEncode v₀ v₁ v₂) h)) ≤
                    ε * (m : ℝ)^2) ∧
                (∀ s₁ ∈ rationalSections v₀, ∀ s₂ ∈ rationalSections v₀,
                  adelicSectionDecode v₀ v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ (s₁, s₂)) = (s₁, s₂)) ∧
                (∀ s s' : ℚ × ℚ,
                  balRem (ternaryHalfMod (ternaryCarryOrder v₁ v₂)) (sectionCoord v₀ s.1) =
                    balRem (ternaryHalfMod (ternaryCarryOrder v₁ v₂)) (sectionCoord v₀ s'.1) ↔
                    (wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s) =
                        wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s') ∨
                      ratPrimeVal 3 (wideGenerator v₁ v₂) + (ternaryCarryOrder v₁ v₂ : ℤ) ≤
                        ratPrimeVal 3
                          (wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s') -
                            wideSection v₁ v₂ (adelicSectionEncode v₀ v₁ v₂ s)))) ∧
                0 ≤ midpointExcess (k • b_pad) a m := by
  obtain ⟨p, b, hp, hb_eq, hb_pos, hRH_sub⟩ := exists_prime_background_subquadraticMidpointTest
  refine ⟨p, b, hp, hb_eq, hb_pos, hRH_sub,
    (riemannHypothesis_iff_singleRule_adelicSectionEncode b hb_pos).1, fun R hR => ?_⟩
  obtain ⟨N, a₁, a₂, hN_gt, ha₁_sig, ha₂_sig, ha₁_gt, ha₂_gt, hsep, hdisj, hlin, hpos_plane⟩ :=
    exists_disjoint_primeSupported_signed_plane R hR (p + 1)
  have hPN : p + 1 ≤ N := hN_gt.le
  let b_pad := padDivisor hPN b
  have hb_pad_pos : 0 < integerProbe N b_pad := by simpa only [b_pad, integerProbe_pad] using hb_pos
  have hdisj_bg : Disjoint (activeConductors b_pad) (activeConductors a₁ ∪ activeConductors a₂) := by
    rw [Finset.disjoint_left]
    intro q hqb hqa
    obtain ⟨i, hi, rfl⟩ := (mem_activeConductors_iff b_pad q).mp hqb
    have hi_le : i.val + 1 ≤ p + 1 := by
      by_contra! hgt
      let e : Fin (p + 1) → Fin N := fun j => ⟨j.val, j.isLt.trans_le hPN⟩
      have hno : ¬ ∃ j : Fin (p + 1), e j = i := by
        rintro ⟨j, rfl⟩; have := j.isLt; dsimp [e] at hgt; omega
      exact hi (Function.extend_apply' _ _ _ hno)
    rcases Finset.mem_union.mp hqa with h1 | h2
    · obtain ⟨j, hj, hjq⟩ := (mem_activeConductors_iff a₁ _).mp h1
      have := ha₁_gt j hj; omega
    · obtain ⟨j, hj, hjq⟩ := (mem_activeConductors_iff a₂ _).mp h2
      have := ha₂_gt j hj; omega
  refine ⟨N, hPN, a₁, a₂, ha₁_sig, ha₂_sig, hdisj, hdisj_bg, hsep, hlin, fun c₁ c₂ => ?_⟩
  let a := c₁ • a₁ + c₂ • a₂
  have ha_alt : a = 0 ∨ 0 < integerProbe N a := by
    by_cases hc0 : c₁ = 0 ∧ c₂ = 0
    · left; dsimp [a]; rw [hc0.1, hc0.2]; simp
    · right
      have hne : c₁ ≠ 0 ∨ c₂ ≠ 0 := by tauto
      exact hpos_plane c₁ c₂ hne
  have ha_nonneg : 0 ≤ integerProbe N a := by
    rcases ha_alt with h0 | hpos
    · rw [h0]; have hz : integerProbe N 0 = 0 := by simpa using integerProbe_smul N 0 (0 : Fin N → ℤ)
      linarith
    · exact hpos.le
  refine ⟨ha_nonneg, fun hne => hpos_plane c₁ c₂ hne, ?_⟩
  filter_upwards [eventually_adelicSectionEncode_midpoint_ray hb_pad_pos ha_alt] with k hk
  filter_upwards [hk] with m ⟨hm, hfib, hex⟩
  refine ⟨hm, hfib, ?_, ?_, ?_, hex⟩
  · intro ε hε
    rw [hfib, Nat.cast_one, Real.log_one]
    exact mul_nonneg hε.le (sq_nonneg _)
  · intro s₁ hs₁ s₂ hs₂
    exact adelicSectionDecode_encode _ _ _
      ((mem_rationalSections_iff _ s₁).mp hs₁).1
      ((mem_rationalSections_iff _ s₂).mp hs₂).1
  · intro s s'
    exact adelicCarryDigit_paid_iff_threeAdic_valuation _ _ _ s s'

/-- Arbitrary finite-rank shared midpoint encoding over the fixed two-atom prime
background `(p, b)`: for every rank `r ≥ 1`, there exist `r` pairwise-disjoint signed
prime-supported generators `a : Fin r → (Fin N → ℤ)` disjoint from `{1, …, p + 1}` on
whose entire `ℤ`-span `⊕_{s=1}^r ℤ (a s)` the single rule `adelicSectionEncode` /
`adelicSectionDecode` succeeds with `maxFibre = 1` for all large `k` and `m`. -/
theorem exists_prime_background_shared_adelicCarry_subspace :
    ∃ (p : ℕ) (b : Fin (p + 1) → ℤ),
      p.Prime ∧ (b = primePair p ∨ b = primeDifference p) ∧
      0 < integerProbe (p + 1) b ∧
      ∀ r : ℕ, 1 ≤ r →
        ∃ (N : ℕ) (hPN : p + 1 ≤ N) (a : Fin r → (Fin N → ℤ)),
          let b_pad := padDivisor hPN b
          (∀ s : Fin r, isSignedPrimeSupported (a s)) ∧
          (∀ s : Fin r, Disjoint (activeConductors b_pad) (activeConductors (a s))) ∧
          (∀ s₁ s₂ : Fin r, s₁ ≠ s₂ → Disjoint (activeConductors (a s₁)) (activeConductors (a s₂))) ∧
          (∀ c : Fin r → ℤ, ((∑ s, c s • a s) = 0 ↔ c = 0)) ∧
          ∀ c : Fin r → ℤ,
            let d := ∑ s, c s • a s
            0 ≤ integerProbe N d ∧
            (c ≠ 0 → 0 < integerProbe N d) ∧
            ∀ᶠ k : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
              let v₀ := m • (k • b_pad)
              let v₁ := m • (k • b_pad + d)
              let v₂ := m • (k • b_pad - d)
              ∃ h : mapsRationalSections (adelicSectionEncode v₀ v₁ v₂) v₀ v₁ v₂,
                maxFibre (restrictRationalSectionMap (adelicSectionEncode v₀ v₁ v₂) h) = 1 ∧
                0 ≤ midpointExcess (k • b_pad) d m := by
  obtain ⟨p, b, hp, hb_eq, hb_pos, _⟩ := exists_prime_background_subquadraticMidpointTest
  refine ⟨p, b, hp, hb_eq, hb_pos, fun r hr => ?_⟩
  obtain ⟨N, a, hN_gt, ha_sig, ha_gt, ha_disj, hlin, hpos_sub⟩ :=
    exists_disjoint_primeSupported_signed_subspace r hr (p + 1)
  have hPN : p + 1 ≤ N := hN_gt.le
  let b_pad := padDivisor hPN b
  have hb_pad_pos : 0 < integerProbe N b_pad := by simpa only [b_pad, integerProbe_pad] using hb_pos
  have hdisj_bg (s : Fin r) : Disjoint (activeConductors b_pad) (activeConductors (a s)) := by
    rw [Finset.disjoint_left]
    intro q hqb hqa
    obtain ⟨i, hi, rfl⟩ := (mem_activeConductors_iff b_pad q).mp hqb
    have hi_le : i.val + 1 ≤ p + 1 := by
      by_contra! hgt
      let e : Fin (p + 1) → Fin N := fun j => ⟨j.val, j.isLt.trans_le hPN⟩
      have hno : ¬ ∃ j : Fin (p + 1), e j = i := by
        rintro ⟨j, rfl⟩; have := j.isLt; dsimp [e] at hgt; omega
      exact hi (Function.extend_apply' _ _ _ hno)
    obtain ⟨j, hj, hjq⟩ := (mem_activeConductors_iff (a s) _).mp hqa
    have := ha_gt s j hj
    omega
  refine ⟨N, hPN, a, ha_sig, hdisj_bg, ha_disj, hlin, fun c => ?_⟩
  let d := ∑ s, c s • a s
  have hd_alt : d = 0 ∨ 0 < integerProbe N d := by
    by_cases hc0 : c = 0
    · left; dsimp [d]; rw [hc0]; simp
    · exact Or.inr (hpos_sub c hc0)
  have hd_nonneg : 0 ≤ integerProbe N d := by
    rcases hd_alt with h0 | hpos
    · rw [h0]; have hz : integerProbe N 0 = 0 := by simpa using integerProbe_smul N 0 (0 : Fin N → ℤ)
      linarith
    · exact hpos.le
  exact ⟨hd_nonneg, hpos_sub c, eventually_adelicSectionEncode_midpoint_ray hb_pad_pos hd_alt⟩

/-! ### 4. Sharp global promotion equivalence and prime-support negative-index law -/

/-- Exact evaluation of `integerProbe` on a difference of two standard basis atoms. -/
theorem integerProbe_twoAtom_diff {N : ℕ} (i j : Fin N) :
    integerProbe N (Pi.single i 1 - Pi.single j 1) =
      2 * (splineSeries 0).re -
        2 * (splineSeries (Real.log ((j : ℝ) + 1) - Real.log ((i : ℝ) + 1))).re := by
  have hij : (atomGram N i j).re = (atomGram N j i).re := by
    have hH : starRingEnd ℂ (atomGram N i j) = atomGram N j i :=
      congr_fun (congr_fun (atomGram_isHermitian N) j) i
    simpa using congr_arg Complex.re hH
  rw [integerProbe_eq_sum]
  simp only [Pi.sub_apply, Pi.single_apply, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hij, atomGram_eq_splineSeries, atomGram_eq_splineSeries, atomGram_eq_splineSeries,
    sub_self, sub_self]
  ring

/-- If RH fails, above any cutoff `P₀` there exist four distinct primes supporting two
disjoint signed two-prime differences `a₁ = e_{p₁} - e_{p₂}` and `a₂ = e_{p₃} - e_{p₄}`
with `integerProbe N a₁ < 0`. -/
theorem exists_twoPrime_diff_neg_integerProbe_of_not_rh (hnotRH : ¬ RiemannHypothesis) (P₀ : ℕ) :
    ∃ (N : ℕ) (a₁ a₂ : Fin N → ℤ),
      P₀ < N ∧
      isSignedPrimeSupported a₁ ∧ isSignedPrimeSupported a₂ ∧
      (activeConductors a₁).card = 2 ∧ (activeConductors a₂).card = 2 ∧
      (∀ i : Fin N, a₁ i ≠ 0 → P₀ < i.val + 1) ∧
      (∀ j : Fin N, a₂ j ≠ 0 → P₀ < j.val + 1) ∧
      Disjoint (activeConductors a₁) (activeConductors a₂) ∧
      (∀ c₁ c₂ : ℤ, (c₁ • a₁ + c₂ • a₂ = 0 ↔ c₁ = 0 ∧ c₂ = 0)) ∧
      integerProbe N a₁ < 0 := by
  obtain ⟨q, hq2, hq_prime, R, _, hpeak, _⟩ :=
    primeTrace_dominates_window_oscillation hnotRH (β := 0) zero_lt_one
      (2 * (splineSeries 0).re + 1) (K := 0) le_rfl 2
  rw [zero_mul, add_zero] at hpeak
  have hg_cont : Continuous (fun t : ℝ => 2 * (splineSeries t).re) :=
    continuous_const.mul (Complex.continuous_re.comp continuous_splineSeries)
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.continuousAt_iff.mp (hg_cont.continuousAt (x := Real.log q)) 1 one_pos
  obtain ⟨U, hU0, hU⟩ :=
    SurfaceOfSpecZ.ScaleLocality.exists_log_prime_avoiding_small_finset
      (γ := 0) (β := 2 / 3) (C := (P₀ + 4 : ℝ))
      le_rfl (by norm_num) (by norm_num) (by norm_num) (by positivity)
  let M_δ := max (4 / δ) 1
  have hMδ_pos : 0 < M_δ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMδ_ge1 : 1 ≤ M_δ := le_max_right _ _
  let T := max U (3 * Real.log M_δ)
  have hTU : U ≤ T := le_max_left _ _
  have hexp_small : 2 * Real.exp ((2 / 3 - 1 : ℝ) * T) ≤ δ / 2 := by
    have hlog_nn : 0 ≤ Real.log M_δ := Real.log_nonneg hMδ_ge1
    have hT_ge : 3 * Real.log M_δ ≤ T := le_max_right _ _
    have hexp_le : Real.exp ((2 / 3 - 1 : ℝ) * T) ≤ Real.exp (-Real.log M_δ) :=
      Real.exp_le_exp.mpr (by linarith only [hT_ge])
    rw [Real.exp_neg, Real.exp_log hMδ_pos] at hexp_le
    have hinv_le : M_δ⁻¹ ≤ δ / 4 := by
      have h4_le : 4 / δ ≤ M_δ := le_max_left _ _
      rw [inv_le_comm₀ hMδ_pos (by positivity : 0 < δ / 4), show (δ / 4)⁻¹ = 4 / δ by ring]
      exact h4_le
    linarith only [hexp_le, hinv_le]
  let E₁ : Finset ℕ := Finset.range (P₀ + 2)
  have hE₁_card : (E₁.card : ℝ) ≤ (P₀ + 4 : ℝ) * Real.exp (0 * T) := by
    rw [Finset.card_range, zero_mul, Real.exp_zero, mul_one]; push_cast; linarith
  obtain ⟨p₁, hp₁_prime, hp₁_not, _, hp₁_le, hp₁_gap⟩ := hU T hTU E₁ hE₁_card
  have hp₁_gt : P₀ + 2 ≤ p₁ := by
    by_contra! hlt; exact hp₁_not (Finset.mem_range.mpr hlt)
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq_prime.pos
  have hlogq_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq_prime.one_lt)
  let u₂ := T + Real.log q
  have hu₂_ge : U ≤ u₂ := by dsimp [u₂]; linarith only [hTU, hlogq_pos]
  let E₂ : Finset ℕ := insert p₁ (Finset.range (P₀ + 2))
  have hE₂_card : (E₂.card : ℝ) ≤ (P₀ + 4 : ℝ) * Real.exp (0 * u₂) := by
    rw [zero_mul, Real.exp_zero, mul_one]
    have hc : E₂.card ≤ (Finset.range (P₀ + 2)).card + 1 := Finset.card_insert_le _ _
    rw [Finset.card_range] at hc
    exact_mod_cast (by omega : E₂.card ≤ P₀ + 4)
  obtain ⟨p₂, hp₂_prime, hp₂_not, _, hp₂_le, hp₂_gap⟩ := hU u₂ hu₂_ge E₂ hE₂_card
  have hp₂_ne_p₁ : p₂ ≠ p₁ := fun h => hp₂_not (h ▸ Finset.mem_insert_self p₁ _)
  have hp₂_gt : P₀ + 2 ≤ p₂ := by
    by_contra! hlt
    exact hp₂_not (Finset.mem_insert_of_mem (Finset.mem_range.mpr hlt))
  have hexp_u₂ : 2 * Real.exp ((2 / 3 - 1 : ℝ) * u₂) ≤ δ / 2 := by
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)).trans hexp_small
    dsimp [u₂]; linarith only [hlogq_pos]
  have hdist_lt : dist (Real.log p₂ - Real.log p₁) (Real.log q) < δ := by
    rw [Real.dist_eq, abs_lt]
    dsimp [u₂] at hp₂_le hp₂_gap
    exact ⟨by linarith only [hp₁_le, hp₂_gap, hexp_u₂, hδ_pos],
           by linarith only [hp₂_le, hp₁_gap, hexp_small, hδ_pos]⟩
  have hg_close := hδ hdist_lt
  rw [Real.dist_eq] at hg_close
  obtain ⟨p₃, hp₃_ge, hp₃_prime⟩ := Nat.exists_infinite_primes (max p₁ p₂ + 1)
  obtain ⟨p₄, hp₄_ge, hp₄_prime⟩ := Nat.exists_infinite_primes (p₃ + 1)
  let N := p₄ + 1
  have hp₁_lt_N : p₁ - 1 < N := by
    have : p₁ ≤ max p₁ p₂ := le_max_left _ _; omega
  have hp₂_lt_N : p₂ - 1 < N := by
    have : p₂ ≤ max p₁ p₂ := le_max_right _ _; omega
  have hp₃_lt_N : p₃ - 1 < N := by omega
  have hp₄_lt_N : p₄ - 1 < N := by omega
  let i₁ : Fin N := ⟨p₁ - 1, hp₁_lt_N⟩
  let i₂ : Fin N := ⟨p₂ - 1, hp₂_lt_N⟩
  let i₃ : Fin N := ⟨p₃ - 1, hp₃_lt_N⟩
  let i₄ : Fin N := ⟨p₄ - 1, hp₄_lt_N⟩
  have hi₁_val : i₁.val + 1 = p₁ := by dsimp [i₁]; omega
  have hi₂_val : i₂.val + 1 = p₂ := by dsimp [i₂]; omega
  have hi₃_val : i₃.val + 1 = p₃ := by dsimp [i₃]; omega
  have hi₄_val : i₄.val + 1 = p₄ := by dsimp [i₄]; omega
  have hi₁₂_ne : i₁ ≠ i₂ := fun h => hp₂_ne_p₁.symm (by have := congrArg Fin.val h; omega)
  have hi₃₄_ne : i₃ ≠ i₄ := fun h => by have := congrArg Fin.val h; omega
  let a₁ : Fin N → ℤ := Pi.single i₁ 1 - Pi.single i₂ 1
  let a₂ : Fin N → ℤ := Pi.single i₃ 1 - Pi.single i₄ 1
  have two_atom_props {x y : Fin N} (hxy : x ≠ y) (hx_p : (x.val + 1).Prime)
      (hy_p : (y.val + 1).Prime) :
      let w := Pi.single x (1 : ℤ) - Pi.single y 1
      isSignedPrimeSupported w ∧ activeConductors w = {x.val + 1, y.val + 1} ∧
      (activeConductors w).card = 2 := by
    intro w
    have hw_x : w x = 1 := by simp [w, Pi.single_eq_of_ne hxy]
    have hw_y : w y = -1 := by simp [w, Pi.single_eq_of_ne hxy.symm]
    have hw_supp {k : Fin N} (hk : w k ≠ 0) : k = x ∨ k = y := by
      by_contra! hne
      apply hk
      simp [w, Pi.single_eq_of_ne hne.1, Pi.single_eq_of_ne hne.2]
    have hact : activeConductors w = {x.val + 1, y.val + 1} := by
      ext m
      rw [mem_activeConductors_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨k, hk, rfl⟩
        rcases hw_supp hk with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨x, by rw [hw_x]; decide, rfl⟩
        · exact ⟨y, by rw [hw_y]; decide, rfl⟩
    have hcard : (activeConductors w).card = 2 := by
      rw [hact, Finset.card_pair (fun h => hxy (Fin.ext (by omega)))]
    refine ⟨⟨?_, ?_, ⟨x, by rw [hw_x]; decide⟩, ⟨y, by rw [hw_y]; decide⟩⟩, hact, hcard⟩
    · intro k hk
      rcases hw_supp hk with rfl | rfl
      · exact hx_p
      · exact hy_p
    · simp [w, Finset.sum_sub_distrib]
  obtain ⟨ha₁_sig, ha₁_act, ha₁_card⟩ :=
    two_atom_props hi₁₂_ne (hi₁_val ▸ hp₁_prime) (hi₂_val ▸ hp₂_prime)
  obtain ⟨ha₂_sig, ha₂_act, ha₂_card⟩ :=
    two_atom_props hi₃₄_ne (hi₃_val ▸ hp₃_prime) (hi₄_val ▸ hp₄_prime)
  have hdisj : Disjoint (activeConductors a₁) (activeConductors a₂) := by
    rw [ha₁_act, ha₂_act, hi₁_val, hi₂_val, hi₃_val, hi₄_val, Finset.disjoint_left]
    intro m hm₁ hm₂
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm₁ hm₂
    have : p₁ ≤ max p₁ p₂ := le_max_left _ _
    have : p₂ ≤ max p₁ p₂ := le_max_right _ _
    rcases hm₁ with rfl | rfl <;> rcases hm₂ with h | h <;> omega
  have hdisj_pt := (disjoint_activeConductors_iff a₁ a₂).mp hdisj
  have hlin (c₁ c₂ : ℤ) : c₁ • a₁ + c₂ • a₂ = 0 ↔ c₁ = 0 ∧ c₂ = 0 := by
    constructor
    · intro h0
      have hv₁ := congrFun h0 i₁
      have hv₂ := congrFun h0 i₃
      have ha₁_i₁ : a₁ i₁ = 1 := by simp [a₁, Pi.single_eq_of_ne hi₁₂_ne]
      have ha₂_i₃ : a₂ i₃ = 1 := by simp [a₂, Pi.single_eq_of_ne hi₃₄_ne]
      have ha₂_i₁ : a₂ i₁ = 0 := (hdisj_pt i₁).resolve_left (by rw [ha₁_i₁]; decide)
      have ha₁_i₃ : a₁ i₃ = 0 := (hdisj_pt i₃).resolve_right (by rw [ha₂_i₃]; decide)
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hv₁ hv₂
      simp only [zsmul_eq_mul, Int.cast_id, ha₁_i₁, ha₂_i₃, ha₂_i₁, ha₁_i₃, mul_one, mul_zero,
        add_zero, zero_add] at hv₁ hv₂
      exact ⟨hv₁, hv₂⟩
    · rintro ⟨rfl, rfl⟩; simp
  have hQ_neg : integerProbe N a₁ < 0 := by
    dsimp [a₁]
    rw [integerProbe_twoAtom_diff]
    have hlog₁ : ((i₁ : ℝ) + 1) = p₁ := by exact_mod_cast hi₁_val
    have hlog₂ : ((i₂ : ℝ) + 1) = p₂ := by exact_mod_cast hi₂_val
    rw [hlog₁, hlog₂]
    linarith only [hpeak, (abs_lt.mp hg_close).1]
  refine ⟨N, a₁, a₂, by dsimp [N]; omega, ha₁_sig, ha₂_sig, ha₁_card, ha₂_card,
    ?_, ?_, hdisj, hlin, hQ_neg⟩
  · intro i hi
    have hm : i.val + 1 ∈ activeConductors a₁ := (mem_activeConductors_iff a₁ _).mpr ⟨i, hi, rfl⟩
    rw [ha₁_act, hi₁_val, hi₂_val] at hm
    rcases Finset.mem_insert.mp hm with h | h
    · omega
    · rw [Finset.mem_singleton] at h; omega
  · intro j hj
    have hm : j.val + 1 ∈ activeConductors a₂ := (mem_activeConductors_iff a₂ _).mpr ⟨j, hj, rfl⟩
    rw [ha₂_act, hi₃_val, hi₄_val] at hm
    have : p₁ ≤ max p₁ p₂ := le_max_left _ _
    rcases Finset.mem_insert.mp hm with h | h
    · omega
    · rw [Finset.mem_singleton] at h; omega

/-- Sharp global promotion equivalence over any positive background `b`: the Riemann
hypothesis is equivalent to `adelicSectionEncode` succeeding across all disjoint
prime-supported signed displacement planes above `P`, and equivalent even to arbitrary
subquadratic-fibre midpoint maps succeeding across all disjoint two-prime-difference planes. -/
theorem riemannHypothesis_iff_all_disjoint_primeSupported_signed_planes {P : ℕ}
    (b : Fin P → ℤ) (hb : 0 < integerProbe P b) :
    (RiemannHypothesis ↔
      ∀ (N : ℕ) (hPN : P ≤ N) (a₁ a₂ : Fin N → ℤ),
        isSignedPrimeSupported a₁ → isSignedPrimeSupported a₂ →
        (∀ i : Fin N, a₁ i ≠ 0 → P < i.val + 1) →
        (∀ j : Fin N, a₂ j ≠ 0 → P < j.val + 1) →
        Disjoint (activeConductors a₁) (activeConductors a₂) →
        ∀ c₁ c₂ : ℤ, ∀ᶠ k : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
          let b_pad := padDivisor hPN b
          let a := c₁ • a₁ + c₂ • a₂
          mapsRationalSections
            (adelicSectionEncode (m • (k • b_pad)) (m • (k • b_pad + a)) (m • (k • b_pad - a)))
            (m • (k • b_pad)) (m • (k • b_pad + a)) (m • (k • b_pad - a))) ∧
    (RiemannHypothesis ↔
      ∀ (N : ℕ) (hPN : P ≤ N) (a₁ a₂ : Fin N → ℤ),
        isSignedPrimeSupported a₁ → isSignedPrimeSupported a₂ →
        (activeConductors a₁).card = 2 → (activeConductors a₂).card = 2 →
        (∀ i : Fin N, a₁ i ≠ 0 → P < i.val + 1) →
        (∀ j : Fin N, a₂ j ≠ 0 → P < j.val + 1) →
        Disjoint (activeConductors a₁) (activeConductors a₂) →
        ∀ c₁ c₂ : ℤ, ∃ᶠ k : ℕ in atTop,
          hasSubquadraticMidpointFibres (k • padDivisor hPN b) (c₁ • a₁ + c₂ • a₂)) := by
  have forward (hRH : RiemannHypothesis) (N : ℕ) (hPN : P ≤ N) (a₁ a₂ : Fin N → ℤ)
      (_ : isSignedPrimeSupported a₁) (_ : isSignedPrimeSupported a₂)
      (_ : ∀ i : Fin N, a₁ i ≠ 0 → P < i.val + 1)
      (_ : ∀ j : Fin N, a₂ j ≠ 0 → P < j.val + 1)
      (_ : Disjoint (activeConductors a₁) (activeConductors a₂)) (c₁ c₂ : ℤ) :
      ∀ᶠ k : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
        let b_pad := padDivisor hPN b
        let a := c₁ • a₁ + c₂ • a₂
        mapsRationalSections
          (adelicSectionEncode (m • (k • b_pad)) (m • (k • b_pad + a)) (m • (k • b_pad - a)))
          (m • (k • b_pad)) (m • (k • b_pad + a)) (m • (k • b_pad - a)) := by
    let b_pad := padDivisor hPN b
    let a := c₁ • a₁ + c₂ • a₂
    have hb_pad : 0 < integerProbe N b_pad := by simpa only [b_pad, integerProbe_pad] using hb
    have ha_alt : a = 0 ∨ 0 < integerProbe N a := by
      by_cases h0 : a = 0
      · exact Or.inl h0
      · exact Or.inr (integerProbe_pos_of_rh hRH h0)
    filter_upwards [eventually_adelicSectionEncode_midpoint_ray hb_pad ha_alt] with k hk
    exact hk.mono fun m ⟨hm, _, _⟩ => hm
  have backward (h : ∀ (N : ℕ) (hPN : P ≤ N) (a₁ a₂ : Fin N → ℤ),
      isSignedPrimeSupported a₁ → isSignedPrimeSupported a₂ →
      (activeConductors a₁).card = 2 → (activeConductors a₂).card = 2 →
      (∀ i : Fin N, a₁ i ≠ 0 → P < i.val + 1) →
      (∀ j : Fin N, a₂ j ≠ 0 → P < j.val + 1) →
      Disjoint (activeConductors a₁) (activeConductors a₂) →
      ∀ c₁ c₂ : ℤ, ∃ᶠ k : ℕ in atTop,
        hasSubquadraticMidpointFibres (k • padDivisor hPN b) (c₁ • a₁ + c₂ • a₂)) :
      RiemannHypothesis := by
    by_contra hnotRH
    obtain ⟨N, a₁, a₂, hPN_lt, ha₁, ha₂, hc₁, hc₂, hg₁, hg₂, hdisj, _, hneg⟩ :=
      exists_twoPrime_diff_neg_integerProbe_of_not_rh hnotRH P
    have hPN : P ≤ N := hPN_lt.le
    have hb_pad : 0 < integerProbe N (padDivisor hPN b) := by
      simpa only [integerProbe_pad] using hb
    have hfreq := h N hPN a₁ a₂ ha₁ ha₂ hc₁ hc₂ hg₁ hg₂ hdisj 1 0
    rw [show (1 : ℤ) • a₁ + (0 : ℤ) • a₂ = a₁ by simp] at hfreq
    have hnn := integerProbe_nonneg_of_subquadraticMidpointFibres (padDivisor hPN b) a₁ hb_pad hfreq
    linarith only [hneg, hnn]
  refine ⟨⟨forward, fun h => backward fun N hPN a₁ a₂ ha₁ ha₂ _ _ hg₁ hg₂ hdisj c₁ c₂ =>
    ((h N hPN a₁ a₂ ha₁ ha₂ hg₁ hg₂ hdisj c₁ c₂).mono fun k hk ε hε =>
      hk.frequently.mono fun m hm => ⟨inducedDivisorSectionMap hm, by
        rw [maxFibre_inducedDivisorSectionMap, maxFibre_adelicSectionEncode_eq_one hm,
          Nat.cast_one, Real.log_one]
        exact mul_nonneg hε.le (sq_nonneg _)⟩).frequently⟩,
    ⟨fun hRH N hPN a₁ a₂ ha₁ ha₂ _ _ hg₁ hg₂ hdisj c₁ c₂ =>
      ((forward hRH N hPN a₁ a₂ ha₁ ha₂ hg₁ hg₂ hdisj c₁ c₂).mono fun k hk ε hε =>
        hk.frequently.mono fun m hm => ⟨inducedDivisorSectionMap hm, by
          rw [maxFibre_inducedDivisorSectionMap, maxFibre_adelicSectionEncode_eq_one hm,
            Nat.cast_one, Real.log_one]
          exact mul_nonneg hε.le (sq_nonneg _)⟩).frequently, backward⟩⟩

private theorem hermNegIndex_submatrix_le {M N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    {ι : Fin M → Fin N} (hι : Function.Injective ι) :
    hermNegIndex (H.submatrix ι ι) ≤ hermNegIndex H := by
  let E : (Fin M → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun x => Function.extend ι x 0
      map_add' := fun x y => by
        funext ℓ
        by_cases hex : ∃ i, ι i = ℓ
        · obtain ⟨i, rfl⟩ := hex; simp [hι.extend_apply]
        · simp [Function.extend_apply' _ _ _ hex]
      map_smul' := fun c x => by
        funext ℓ
        by_cases hex : ∃ i, ι i = ℓ
        · obtain ⟨i, rfl⟩ := hex; simp [hι.extend_apply]
        · simp [Function.extend_apply' _ _ _ hex] }
  have hE_inj : Function.Injective E := by
    intro x y hxy
    funext i
    have hi := congrFun hxy (ι i)
    simpa only [E, LinearMap.coe_mk, AddHom.coe_mk, hι.extend_apply] using hi
  have hquad (x : Fin M → ℂ) : hermQuad (-H) (E x) = hermQuad (-(H.submatrix ι ι)) x := by
    have hoff (ℓ : Fin N) (hℓ : ℓ ∉ Finset.univ.image ι) : E x ℓ = 0 :=
      Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    unfold hermQuad
    simp only [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re, neg_inj]
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)) fun ℓ _ hℓ => by
      simp only [hoff ℓ hℓ, star_zero, zero_mul, Finset.sum_const_zero]]
    rw [Finset.sum_image fun i _ j _ h => hι h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)) fun ℓ _ hℓ => by
      rw [hoff ℓ hℓ, mul_zero, mul_zero]]
    rw [Finset.sum_image fun j _ k _ h => hι h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [E, LinearMap.coe_mk, AddHom.coe_mk, hι.extend_apply, Matrix.submatrix_apply]
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-(H.submatrix ι ι))
  have hmap : IsPosDefOn (-H) (W.map E) := by
    rintro y ⟨x, hx, rfl⟩ hy0
    have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
    rw [hquad]
    exact hW x hx hx0
  have heq : Module.finrank ℂ (W.map E) = Module.finrank ℂ W :=
    ((Submodule.equivMapOfInjective E hE_inj W).symm).finrank_eq
  unfold hermNegIndex
  rw [← hrank, ← heq]
  exact finrank_le_posIndex hmap

private theorem exists_primeTuple_log_approx (M P₀ : ℕ) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ T : ℝ, U ≤ T →
      ∃ (N : ℕ) (ι : Fin M → Fin N),
        Function.Injective ι ∧
        (∀ i : Fin M, ((ι i).val + 1).Prime ∧ P₀ < (ι i).val + 1 ∧
          Real.log ((ι i).val + 1) ≤ T + Real.log ((i : ℝ) + 1) ∧
          (T + Real.log ((i : ℝ) + 1)) - Real.log ((ι i).val + 1) ≤
            2 * Real.exp (-(1 / 3 : ℝ) * T)) := by
  obtain ⟨U, hU0, hU⟩ :=
    SurfaceOfSpecZ.ScaleLocality.exists_log_prime_avoiding_small_finset
      (γ := 0) (β := 2 / 3) (C := (M + P₀ + 3 : ℝ))
      le_rfl (by norm_num) (by norm_num) (by norm_num) (by positivity)
  refine ⟨U, hU0, fun T hTU => ?_⟩
  have hind : ∀ k : ℕ, k ≤ M →
      ∃ f : Fin k → ℕ, Function.Injective f ∧
        ∀ i : Fin k, (f i).Prime ∧ P₀ < f i ∧
          Real.log (f i) ≤ T + Real.log ((i : ℝ) + 1) ∧
          (T + Real.log ((i : ℝ) + 1)) - Real.log (f i) ≤
            2 * Real.exp (-(1 / 3 : ℝ) * T) := by
    intro k
    induction k with
    | zero =>
      exact fun _ => ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ k ih =>
      intro hkM
      obtain ⟨f, hf_inj, hf_props⟩ := ih (by omega)
      let E : Finset ℕ := Finset.range (P₀ + 2) ∪ Finset.univ.image f
      let u := T + Real.log ((k : ℝ) + 1)
      have hlog_nn : 0 ≤ Real.log ((k : ℝ) + 1) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k])
      have hu_ge : U ≤ u := by dsimp [u]; linarith only [hTU, hlog_nn]
      have hE_card : (E.card : ℝ) ≤ (M + P₀ + 3 : ℝ) * Real.exp (0 * u) := by
        rw [zero_mul, Real.exp_zero, mul_one]
        have hc₁ : E.card ≤ (Finset.range (P₀ + 2)).card + (Finset.univ.image f).card :=
          Finset.card_union_le _ _
        have hc₂ : (Finset.univ.image f).card ≤ k :=
          (Finset.card_image_le (s := Finset.univ) (f := f)).trans_eq
            (by rw [Finset.card_univ, Fintype.card_fin])
        rw [Finset.card_range] at hc₁
        exact_mod_cast (by omega : E.card ≤ M + P₀ + 3)
      obtain ⟨q, hq_prime, hq_not, _, hq_le, hq_gap⟩ := hU u hu_ge E hE_card
      have hq_gt : P₀ < q := by
        by_contra! hle
        exact hq_not (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
      have hq_ne (i : Fin k) : q ≠ f i := fun h =>
        hq_not (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩))
      have hexp_le : 2 * Real.exp ((2 / 3 - 1 : ℝ) * u) ≤ 2 * Real.exp (-(1 / 3 : ℝ) * T) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        dsimp [u]; linarith only [hlog_nn]
      let f' : Fin (k + 1) → ℕ := fun j => if h : j.val < k then f ⟨j.val, h⟩ else q
      refine ⟨f', ?_, ?_⟩
      · intro j₁ j₂ hj
        dsimp only [f'] at hj
        by_cases h₁ : j₁.val < k <;> by_cases h₂ : j₂.val < k
        · rw [dif_pos h₁, dif_pos h₂] at hj
          exact Fin.ext (Fin.mk.inj_iff.mp (hf_inj hj))
        · rw [dif_pos h₁, dif_neg h₂] at hj
          exact (hq_ne ⟨j₁.val, h₁⟩ hj.symm).elim
        · rw [dif_neg h₁, dif_pos h₂] at hj
          exact (hq_ne ⟨j₂.val, h₂⟩ hj).elim
        · have := j₁.isLt; have := j₂.isLt
          exact Fin.ext (by omega)
      · intro j
        dsimp only [f']
        split_ifs with hj
        · exact hf_props ⟨j.val, hj⟩
        · have hj_eq : (j : ℝ) = (k : ℝ) := by
            have : j.val = k := by omega
            exact_mod_cast this
          rw [hj_eq]
          exact ⟨hq_prime, hq_gt, hq_le, hq_gap.trans hexp_le⟩
  obtain ⟨f, hf_inj, hf_props⟩ := hind M le_rfl
  let N := (Finset.univ.image f).sup id + 1
  let ι : Fin M → Fin N := fun i => ⟨f i - 1, by
    have hle : f i ≤ (Finset.univ.image f).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem f (Finset.mem_univ i))
    have hpos : 0 < f i := (hf_props i).1.pos
    omega⟩
  have hι_val (i : Fin M) : (ι i).val + 1 = f i := by
    dsimp [ι]; have := (hf_props i).1.pos; omega
  refine ⟨N, ι, ?_, fun i => ?_⟩
  · intro i j hij
    have h := congrArg Fin.val hij
    have hi := hι_val i; have hj := hι_val j
    exact hf_inj (by omega)
  · have hc : ((ι i : ℕ) : ℝ) + 1 = (f i : ℝ) := by exact_mod_cast hι_val i
    rw [hι_val i, hc]
    exact hf_props i

/-- Subtype of `M`-element embeddings into `Fin N` supported solely on primes above `P₀`. -/
abbrev PrimeConductorEmbedding (M N P₀ : ℕ) :=
  {ι : Fin M → Fin N // Function.Injective ι ∧ ∀ i : Fin M, ((ι i).val + 1).Prime ∧ P₀ < (ι i).val + 1}

private theorem exists_primeSubmatrix_tendsto_atomGram (M P₀ : ℕ) :
    ∃ (Nseq : ℕ → ℕ) (ιseq : ∀ n, Fin M → Fin (Nseq n)),
      (∀ n, Function.Injective (ιseq n)) ∧
      (∀ n i, ((ιseq n i).val + 1).Prime ∧ P₀ < (ιseq n i).val + 1) ∧
      (∀ i j : Fin M,
        Tendsto (fun n : ℕ => atomGram (Nseq n) (ιseq n i) (ιseq n j))
          atTop (𝓝 (atomGram M i j))) := by
  obtain ⟨U, _, hU⟩ := exists_primeTuple_log_approx M P₀
  have hseq (n : ℕ) := hU (max U (n : ℝ)) (le_max_left _ _)
  choose Nseq ιseq hι_inj hι_props using hseq
  refine ⟨Nseq, ιseq, hι_inj, fun n i => ⟨(hι_props n i).1, (hι_props n i).2.1⟩, fun i j => ?_⟩
  rw [atomGram_eq_splineSeries M i j]
  have hzero : Tendsto (fun n : ℕ => (6 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hexp_bound (n : ℕ) (hn1 : 1 ≤ n) :
      2 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ)) ≤ (6 : ℝ) / (n : ℝ) := by
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hlin : (1 / 3 : ℝ) * (n : ℝ) ≤ Real.exp ((1 / 3 : ℝ) * (n : ℝ)) := by
      linarith [Real.add_one_le_exp ((1 / 3 : ℝ) * (n : ℝ))]
    rw [neg_mul, Real.exp_neg]
    have hinv := inv_anti₀ (by positivity : 0 < (1 / 3 : ℝ) * (n : ℝ)) hlin
    have hrew : ((1 / 3 : ℝ) * (n : ℝ))⁻¹ = (3 : ℝ) / (n : ℝ) := by field_simp
    rw [hrew] at hinv
    calc 2 * (Real.exp ((1 / 3 : ℝ) * (n : ℝ)))⁻¹ ≤ 2 * ((3 : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 6 / (n : ℝ) := by ring
  have harg : Tendsto
      (fun n : ℕ => Real.log (((ιseq n i).val : ℝ) + 1) - Real.log (((ιseq n j).val : ℝ) + 1))
      atTop (𝓝 (Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1))) := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt U
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa only [sub_zero] using tendsto_const_nhds.sub hzero)
      (by simpa only [add_zero] using tendsto_const_nhds.add hzero) ?_ ?_
    · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
      have hmax : max U (n : ℝ) = (n : ℝ) :=
        max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
      have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
      have hi := (hι_props n i).2.2
      have hj := (hι_props n j).2.2
      rw [hmax] at hi hj
      linarith only [hi.2, hj.1, hb]
    · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
      have hmax : max U (n : ℝ) = (n : ℝ) :=
        max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
      have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
      have hi := (hι_props n i).2.2
      have hj := (hι_props n j).2.2
      rw [hmax] at hi hj
      linarith only [hi.1, hj.2, hb]
  refine (continuous_splineSeries.tendsto _).comp harg |> fun h => h.congr fun n => ?_
  dsimp only [Function.comp_apply]
  rw [atomGram_eq_splineSeries]

/-- Every nonzero zero-sum integer divisor `u : Fin M → ℤ` (`∑ i, u i = 0`) can be
approximated arbitrarily closely in `integerProbe` by a genuinely signed
prime-supported divisor `a : Fin N → ℤ` whose active primes all exceed `P₀`. -/
theorem exists_signed_primeSupported_integerProbe_near {M : ℕ} {u : Fin M → ℤ}
    (hu_ne : u ≠ 0) (hu_sum : (∑ i : Fin M, u i) = 0) (P₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (a : Fin N → ℤ),
      P₀ < N ∧
      isSignedPrimeSupported a ∧
      (∀ ℓ : Fin N, a ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
      |integerProbe N a - integerProbe M u| < ε := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by simpa [funext_iff] using hu_ne
  have hpos_u : ∃ i₁ : Fin M, 0 < u i₁ := by
    by_contra! hle
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · have hsplit := Finset.add_sum_erase Finset.univ u (Finset.mem_univ i₀)
      have hrest : ∑ i ∈ Finset.univ.erase i₀, u i ≤ 0 := Finset.sum_nonpos fun i _ => hle i
      linarith only [hsplit, hu_sum, hrest, hneg]
    · exact (hle i₀).not_gt hpos
  have hneg_u : ∃ i₂ : Fin M, u i₂ < 0 := by
    by_contra! hge
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · exact (hge i₀).not_gt hneg
    · have hsplit := Finset.add_sum_erase Finset.univ u (Finset.mem_univ i₀)
      have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, u i := Finset.sum_nonneg fun i _ => hge i
      linarith only [hsplit, hu_sum, hrest, hpos]
  obtain ⟨i₁, hi₁⟩ := hpos_u
  obtain ⟨i₂, hi₂⟩ := hneg_u
  obtain ⟨Nseq, ιseq, hι_inj, hι_p, hconv⟩ := exists_primeSubmatrix_tendsto_atomGram M P₀
  let a (n : ℕ) : Fin (Nseq n) → ℤ := Function.extend (ιseq n) u 0
  have hprobe_eq (n : ℕ) :
      integerProbe (Nseq n) (a n) =
        ∑ i : Fin M, ∑ j : Fin M,
          (atomGram (Nseq n) (ιseq n i) (ιseq n j)).re * (u i : ℝ) * (u j : ℝ) := by
    rw [integerProbe_eq_sum]
    have houter : (∑ ℓ : Fin (Nseq n), ∑ ℓ' : Fin (Nseq n),
        (atomGram (Nseq n) ℓ ℓ').re * (a n ℓ : ℝ) * (a n ℓ' : ℝ)) =
        ∑ ℓ : Fin (Nseq n),
          (∑ ℓ' : Fin (Nseq n), (atomGram (Nseq n) ℓ ℓ').re * (a n ℓ' : ℝ)) * (a n ℓ : ℝ) := by
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun ℓ' _ => by ring
    rw [houter, show a n = Function.extend (ιseq n) u 0 from rfl,
      sum_extend_zero (hι_inj n)
        (fun ℓ => ∑ ℓ' : Fin (Nseq n), (atomGram (Nseq n) ℓ ℓ').re *
          ((Function.extend (ιseq n) u 0 ℓ' : ℤ) : ℝ)) u]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_extend_zero (hι_inj n) (fun ℓ' => (atomGram (Nseq n) (ιseq n i) ℓ').re) u,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hprobe_lim : Tendsto (fun n : ℕ => integerProbe (Nseq n) (a n))
      atTop (𝓝 (integerProbe M u)) := by
    rw [integerProbe_eq_sum M u]
    refine (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ =>
        (((Complex.continuous_re.tendsto _).comp (hconv i j)).mul_const (u i : ℝ)).mul_const
          (u j : ℝ)).congr fun n => (hprobe_eq n).symm
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp hprobe_lim ε hε).exists
  rw [Real.dist_eq] at hn
  have hN_gt : P₀ < Nseq n := by
    have h1 := (hι_p n i₁).2
    have h2 := (ιseq n i₁).isLt
    omega
  have ha_supp {ℓ : Fin (Nseq n)} (hℓ : a n ℓ ≠ 0) :
      (ℓ.val + 1).Prime ∧ P₀ < ℓ.val + 1 := by
    by_cases hex : ∃ i : Fin M, ιseq n i = ℓ
    · obtain ⟨i, rfl⟩ := hex
      exact hι_p n i
    · exact (hℓ (Function.extend_apply' _ _ _ hex)).elim
  have ha_sum : (∑ ℓ : Fin (Nseq n), a n ℓ) = 0 := by
    have hreal : (∑ ℓ : Fin (Nseq n), (a n ℓ : ℝ)) = 0 := by
      have h1 := sum_extend_zero (hι_inj n) (fun _ => (1 : ℝ)) u
      simp only [one_mul] at h1
      have hu_r : (∑ i : Fin M, (u i : ℝ)) = 0 := by exact_mod_cast hu_sum
      exact h1.trans hu_r
    exact_mod_cast hreal
  exact ⟨Nseq n, a n, hN_gt,
    ⟨fun ℓ hℓ => (ha_supp hℓ).1, ha_sum,
     ⟨ιseq n i₁, by simpa only [a, (hι_inj n).extend_apply] using hi₁⟩,
     ⟨ιseq n i₂, by simpa only [a, (hι_inj n).extend_apply] using hi₂⟩⟩,
    fun ℓ hℓ => (ha_supp hℓ).2, hn⟩

/-- Prime-supported Gram submatrices above any finite cutoff `P₀` carry the full
off-line zero index `(rightZeros zetaZeroConfig).encard`. -/
theorem rightZeros_encard_eq_iSup_primeSubmatrix (P₀ : ℕ) :
    (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard =
      ⨆ (M : ℕ) (N : ℕ) (ι : PrimeConductorEmbedding M N P₀),
        (hermNegIndex ((atomGram N).submatrix ι.val ι.val) : ℕ∞) := by
  rw [rightZeros_encard_eq_sectionIndex]
  simp only [sectionMatrix_eq_atomGram]
  refine le_antisymm ?_ ?_
  · apply iSup_le
    intro M
    obtain ⟨Nseq, ιseq, hι_inj, hι_p, hconv⟩ := exists_primeSubmatrix_tendsto_atomGram M P₀
    let Hseq (n : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
      (atomGram (Nseq n)).submatrix (ιseq n) (ιseq n)
    obtain ⟨n, hn⟩ :=
      (eventually_le_hermNegIndex (H := Hseq) (atomGram_isHermitian M) hconv).exists
    let emb : PrimeConductorEmbedding M (Nseq n) P₀ := ⟨ιseq n, hι_inj n, hι_p n⟩
    calc (hermNegIndex (atomGram M) : ℕ∞)
        ≤ (hermNegIndex (Hseq n) : ℕ∞) := by exact_mod_cast hn
      _ ≤ ⨆ (M' : ℕ) (N' : ℕ) (ι' : PrimeConductorEmbedding M' N' P₀),
            (hermNegIndex ((atomGram N').submatrix ι'.val ι'.val) : ℕ∞) :=
          le_iSup_of_le M (le_iSup_of_le (Nseq n) (le_iSup _ emb))
  · apply iSup_le; intro M; apply iSup_le; intro N; apply iSup_le; intro ι
    calc (hermNegIndex ((atomGram N).submatrix ι.val ι.val) : ℕ∞)
        ≤ (hermNegIndex (atomGram N) : ℕ∞) := by
          exact_mod_cast hermNegIndex_submatrix_le (atomGram N) ι.property.1
      _ ≤ ⨆ K : ℕ, (hermNegIndex (atomGram K) : ℕ∞) := le_iSup _ N

end GaloisForLFunctions.CountingHolography.Sections
