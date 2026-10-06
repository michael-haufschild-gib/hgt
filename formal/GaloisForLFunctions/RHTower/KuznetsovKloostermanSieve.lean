import GaloisForLFunctions.RHTower.KuznetsovSqrtSeparation
import GaloisForLFunctions.RHTower.Sieve.KloostermanSum

/-!
# Bilinear forms with Kloosterman sums and the phase `e(2θ√(mn)/c)`

**The large sieve for one modulus.** For `S ⊆ (L₀, L₀ + L]`,

`Σ_{y mod c} |Σ_{n ∈ S} β_n e(ny/c)|² ≤ (L + c) Σ_{n ∈ S} |β_n|²`

(`sum_norm_sq_additive_le`): orthogonality gives `c Σ_{n ≡ n'} β_n β̄_{n'}`, and each residue class
meets the interval in at most `L/c + 1` points.

**DI (1.26), single-modulus form.** For `m, n ∈ (N, 2N]`, separating `e(2θ√(mn)/c)` by a Fourier
integral in `log m + log n` and applying the above to each frequency,

`|Σ_{m,n} ᾱ_m α_n S(m, n; c) e(2θ√(mn)/c)| ≤ C (1 + |θ|N/c)(N + c) Σ |α_n|²`

with an absolute constant `C` (`exists_bilinear_kloosterman_le`).
-/

open MeasureTheory Set Filter Complex
open scoped FourierTransform ComplexConjugate

namespace GaloisForLFunctions.RHTower.KuznetsovSeparation

open RHTower.Sieve

noncomputable section

/-! ## Orthogonality and the large sieve for one modulus -/

theorem sum_stdAddChar_mul (c : ℕ) [NeZero c] (k : ZMod c) :
    ∑ y : ZMod c, ZMod.stdAddChar (k * y) = if k = 0 then (c : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp [ZMod.card]
  · have h := ZMod.isPrimitive_stdAddChar c hk
    exact AddChar.sum_eq_zero_of_ne_one h

theorem card_filter_modEq_le (L₀ L c v : ℕ) (hc : 0 < c) :
    (((Finset.Ioc L₀ (L₀ + L)).filter fun x => x ≡ v [MOD c]).card : ℝ) ≤ (L : ℝ) / c + 1 := by
  have h := Nat.Ioc_filter_modEq_card L₀ (L₀ + L) hc v
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_natCast] at h'
  push_cast at h'
  rw [h']
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  refine max_le ?_ (by positivity)
  have key : ∀ x y : ℚ, ((⌊x⌋ : ℤ) : ℝ) - ((⌊y⌋ : ℤ) : ℝ) ≤ ((x - y + 1 : ℚ) : ℝ) := fun x y => by
    have h1 := Int.floor_le x
    have h2 := Int.lt_floor_add_one y
    have : ((⌊x⌋ : ℤ) : ℚ) - ((⌊y⌋ : ℤ) : ℚ) ≤ x - y + 1 := by linarith
    exact_mod_cast this
  refine (key _ _).trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

/-- **The large sieve for one modulus.** -/
theorem sum_norm_sq_additive_le (c : ℕ) [NeZero c] (L₀ L : ℕ) (β : ℕ → ℂ) :
    ∑ y : ZMod c, ‖∑ n ∈ Finset.Ioc L₀ (L₀ + L), β n * ZMod.stdAddChar ((n : ZMod c) * y)‖ ^ 2 ≤
      ((L : ℝ) + c) * ∑ n ∈ Finset.Ioc L₀ (L₀ + L), ‖β n‖ ^ 2 := by
  classical
  set S := Finset.Ioc L₀ (L₀ + L)
  have hc : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  set δ : ℕ → ℕ → ℂ := fun n n' => if (n : ZMod c) = (n' : ZMod c) then 1 else 0
  -- the complex identity
  have hid : ((∑ y : ZMod c, ‖∑ n ∈ S, β n * ZMod.stdAddChar ((n : ZMod c) * y)‖ ^ 2 : ℝ) : ℂ) =
      (c : ℂ) * ∑ n ∈ S, ∑ n' ∈ S, δ n n' * (β n * conj (β n')) := by
    push_cast
    have hpt : ∀ y : ZMod c, ((‖∑ n ∈ S, β n * ZMod.stdAddChar ((n : ZMod c) * y)‖ : ℝ) : ℂ) ^ 2 =
        ∑ n ∈ S, ∑ n' ∈ S, β n * conj (β n') *
          ZMod.stdAddChar (((n : ZMod c) - (n' : ZMod c)) * y) := fun y => by
      rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
      have hc1 : conj (ZMod.stdAddChar ((n' : ZMod c) * y)) =
          ZMod.stdAddChar (-((n' : ZMod c) * y)) := (AddChar.map_neg_eq_conj _ _).symm
      have hm : ZMod.stdAddChar ((n : ZMod c) * y) * ZMod.stdAddChar (-((n' : ZMod c) * y)) =
          ZMod.stdAddChar (((n : ZMod c) - (n' : ZMod c)) * y) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
      rw [RingHom.map_mul (starRingEnd ℂ), hc1, ← hm]
      ring
    simp_rw [hpt]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [← Finset.mul_sum, sum_stdAddChar_mul]
    simp only [δ]
    by_cases h : (n : ZMod c) = (n' : ZMod c)
    · rw [if_pos (sub_eq_zero.2 h), if_pos h]; ring
    · rw [if_neg (sub_ne_zero.2 h), if_neg h]; ring
  -- norms
  have hnorm : ∑ y : ZMod c, ‖∑ n ∈ S, β n * ZMod.stdAddChar ((n : ZMod c) * y)‖ ^ 2 ≤
      c * ∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * (‖β n‖ * ‖β n'‖) := by
    have h := congrArg norm hid
    rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun y _ => by positivity),
      norm_mul, Complex.norm_natCast] at h
    rw [h]
    gcongr
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun n' _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have hδ : ∀ n n', ‖δ n n'‖ = if (n : ZMod c) = (n' : ZMod c) then 1 else 0 := fun n n' => by
    simp only [δ]; split_ifs <;> simp
  -- AM–GM and symmetry
  have hamgm : ∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * (‖β n‖ * ‖β n'‖) ≤
      ∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * ‖β n‖ ^ 2 := by
    have hsym : ∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * ‖β n'‖ ^ 2 =
        ∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * ‖β n‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
      rw [hδ, hδ]
      by_cases h : (n' : ZMod c) = (n : ZMod c)
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    have hle : ∀ n n', ‖δ n n'‖ * (‖β n‖ * ‖β n'‖) ≤
        (‖δ n n'‖ * ‖β n‖ ^ 2 + ‖δ n n'‖ * ‖β n'‖ ^ 2) / 2 := fun n n' => by
      have := norm_nonneg (δ n n')
      nlinarith [sq_nonneg (‖β n‖ - ‖β n'‖), mul_nonneg this (sq_nonneg (‖β n‖ - ‖β n'‖))]
    calc ∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * (‖β n‖ * ‖β n'‖)
        ≤ ∑ n ∈ S, ∑ n' ∈ S, (‖δ n n'‖ * ‖β n‖ ^ 2 + ‖δ n n'‖ * ‖β n'‖ ^ 2) / 2 :=
          Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun n' _ => hle n n'
      _ = ((∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * ‖β n‖ ^ 2) +
            ∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * ‖β n'‖ ^ 2) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ = _ := by rw [hsym]; ring
  -- counting
  have hcount : ∀ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ ≤ (L : ℝ) / c + 1 := fun n _ => by
    simp_rw [hδ]
    rw [Finset.sum_boole]
    have hset : (S.filter fun n' : ℕ => (n : ZMod c) = (n' : ZMod c)) =
        S.filter fun n' : ℕ => n' ≡ n [MOD c] := by
      ext n'
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, (ZMod.natCast_eq_natCast_iff _ _ _).1 h2.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, ((ZMod.natCast_eq_natCast_iff _ _ _).2 h2).symm⟩
    rw [hset]
    exact card_filter_modEq_le L₀ L c n hc
  calc ∑ y : ZMod c, ‖∑ n ∈ S, β n * ZMod.stdAddChar ((n : ZMod c) * y)‖ ^ 2
      ≤ c * ∑ n ∈ S, ∑ n' ∈ S, ‖δ n n'‖ * ‖β n‖ ^ 2 :=
        hnorm.trans (mul_le_mul_of_nonneg_left hamgm hc'.le)
    _ = c * ∑ n ∈ S, (∑ n' ∈ S, ‖δ n n'‖) * ‖β n‖ ^ 2 := by
        congr 1; refine Finset.sum_congr rfl fun n _ => ?_; rw [Finset.sum_mul]
    _ ≤ c * ∑ n ∈ S, ((L : ℝ) / c + 1) * ‖β n‖ ^ 2 := by
        gcongr with n hn
        exact hcount n hn
    _ = ((L : ℝ) + c) * ∑ n ∈ S, ‖β n‖ ^ 2 := by
        rw [← Finset.mul_sum, ← mul_assoc]; congr 1; field_simp

/-! ## The bilinear Kloosterman form -/

theorem sum_units_le_sum_all (c : ℕ) [NeZero c] (f : ZMod c → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ x : (ZMod c)ˣ, f (x : ZMod c) ≤ ∑ y : ZMod c, f y := by
  classical
  have hinj : Set.InjOn (fun x : (ZMod c)ˣ => (x : ZMod c)) (Finset.univ : Finset (ZMod c)ˣ) :=
    fun x _ y _ h => Units.ext h
  rw [← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun y _ _ => hf y

/-- `|Σ_{m,n} β'_m β_n S(m, n; c)| ≤ (N + c) (Σ|β'|² + Σ|β|²)/2` for `m, n ∈ (N, 2N]`. -/
theorem norm_bilinear_kloostermanSum_le (c : ℕ) [NeZero c] (N : ℕ) (β' β : ℕ → ℂ) :
    ‖∑ m ∈ Finset.Ioc N (N + N), ∑ n ∈ Finset.Ioc N (N + N),
        β' m * β n * kloostermanSum c (m : ZMod c) (n : ZMod c)‖ ≤
      ((N : ℝ) + c) * ((∑ m ∈ Finset.Ioc N (N + N), ‖β' m‖ ^ 2) +
        ∑ n ∈ Finset.Ioc N (N + N), ‖β n‖ ^ 2) / 2 := by
  set S := Finset.Ioc N (N + N)
  set P : ZMod c → ℂ := fun y => ∑ m ∈ S, β' m * ZMod.stdAddChar ((m : ZMod c) * y)
  set Q : ZMod c → ℂ := fun y => ∑ n ∈ S, β n * ZMod.stdAddChar ((n : ZMod c) * y)
  have hexp : ∑ m ∈ S, ∑ n ∈ S, β' m * β n * kloostermanSum c (m : ZMod c) (n : ZMod c) =
      ∑ x : (ZMod c)ˣ, P x * Q ((x⁻¹ : (ZMod c)ˣ) : ZMod c) := by
    calc ∑ m ∈ S, ∑ n ∈ S, β' m * β n * kloostermanSum c (m : ZMod c) (n : ZMod c)
        = ∑ m ∈ S, ∑ n ∈ S, ∑ x : (ZMod c)ˣ, β' m * ZMod.stdAddChar ((m : ZMod c) * (x : ZMod c)) *
            (β n * ZMod.stdAddChar ((n : ZMod c) * ((x⁻¹ : (ZMod c)ˣ) : ZMod c))) := by
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
          rw [kloostermanSum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [kloostermanPhase, AddChar.map_add_eq_mul]
          ring
      _ = ∑ m ∈ S, ∑ x : (ZMod c)ˣ, ∑ n ∈ S, β' m * ZMod.stdAddChar ((m : ZMod c) * (x : ZMod c)) *
            (β n * ZMod.stdAddChar ((n : ZMod c) * ((x⁻¹ : (ZMod c)ˣ) : ZMod c))) :=
          Finset.sum_congr rfl fun m _ => Finset.sum_comm
      _ = ∑ x : (ZMod c)ˣ, ∑ m ∈ S, ∑ n ∈ S, β' m * ZMod.stdAddChar ((m : ZMod c) * (x : ZMod c)) *
            (β n * ZMod.stdAddChar ((n : ZMod c) * ((x⁻¹ : (ZMod c)ˣ) : ZMod c))) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun x _ => by
          simp only [P, Q]
          rw [Finset.sum_mul_sum]
  have hP := sum_norm_sq_additive_le c N N β'
  have hQ := sum_norm_sq_additive_le c N N β
  have hQinv : ∑ x : (ZMod c)ˣ, ‖Q ((x⁻¹ : (ZMod c)ˣ) : ZMod c)‖ ^ 2 =
      ∑ x : (ZMod c)ˣ, ‖Q (x : ZMod c)‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.inv (ZMod c)ˣ) _ _ fun x => rfl
  rw [hexp]
  calc ‖∑ x : (ZMod c)ˣ, P x * Q ((x⁻¹ : (ZMod c)ˣ) : ZMod c)‖
      ≤ ∑ x : (ZMod c)ˣ, ‖P x‖ * ‖Q ((x⁻¹ : (ZMod c)ˣ) : ZMod c)‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => norm_mul _ _))
    _ ≤ ∑ x : (ZMod c)ˣ, (‖P x‖ ^ 2 + ‖Q ((x⁻¹ : (ZMod c)ˣ) : ZMod c)‖ ^ 2) / 2 :=
        Finset.sum_le_sum fun x _ => by
          nlinarith [sq_nonneg (‖P x‖ - ‖Q ((x⁻¹ : (ZMod c)ˣ) : ZMod c)‖)]
    _ = ((∑ x : (ZMod c)ˣ, ‖P x‖ ^ 2) + ∑ x : (ZMod c)ˣ, ‖Q (x : ZMod c)‖ ^ 2) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hQinv]
    _ ≤ ((∑ y : ZMod c, ‖P y‖ ^ 2) + ∑ y : ZMod c, ‖Q y‖ ^ 2) / 2 := by
        gcongr
        · exact sum_units_le_sum_all c (fun y => ‖P y‖ ^ 2) fun y => by positivity
        · exact sum_units_le_sum_all c (fun y => ‖Q y‖ ^ 2) fun y => by positivity
    _ ≤ (((N : ℝ) + c) * ∑ m ∈ S, ‖β' m‖ ^ 2 + ((N : ℝ) + c) * ∑ n ∈ S, ‖β n‖ ^ 2) / 2 := by
        gcongr
    _ = _ := by ring

/-! ## The twisted form -/

theorem exp_half_log_add {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    Real.exp ((Real.log m + Real.log n) / 2) = Real.sqrt (m * n) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (mul_pos hm hn), Real.log_mul hm.ne' hn.ne']
  ring_nf

theorem log_window {N m : ℕ} (hN : 1 ≤ N) (hm : m ∈ Finset.Ioc N (N + N)) :
    Real.log N < Real.log m ∧ Real.log m ≤ Real.log N + Real.log 2 := by
  rw [Finset.mem_Ioc] at hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · exact Real.log_lt_log hN0 (by exact_mod_cast hm.1)
  · rw [← Real.log_mul hN0.ne' (by norm_num)]
    exact Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le hN hm.1.le))
      (by have : (m : ℝ) ≤ N + N := by exact_mod_cast hm.2
          linarith)

/-- **DI (1.26), single-modulus form**:
`|Σ_{m,n ∈ (N,2N]} ᾱ_m α_n S(m,n;c) e(2θ√(mn)/c)| ≤ C (1 + |θ|N/c)(N + c) Σ |α_n|²`. -/
theorem exists_bilinear_kloosterman_phase_le : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ) [NeZero c] (N : ℕ),
    1 ≤ N → ∀ (α : ℕ → ℂ) (θ : ℝ),
      ‖∑ m ∈ Finset.Ioc N (N + N), ∑ n ∈ Finset.Ioc N (N + N),
          conj (α m) * α n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
            cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * Complex.I)‖ ≤
        C * (1 + |θ| * N / c) * ((N : ℝ) + c) * ∑ n ∈ Finset.Ioc N (N + N), ‖α n‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hsep⟩ := exists_sqrt_phase_separation
  refine ⟨2 * C₀, by positivity, fun c _ N hN α θ => ?_⟩
  set S := Finset.Ioc N (N + N)
  have hc : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set a := 2 * Real.log N
  set A := 2 * θ / c
  obtain ⟨hint, hL1, hrep⟩ := hsep a A
  set φ := 𝓕 (sepFun a A)
  set e : ℕ → ℝ → ℂ := fun m t => cexp (((2 * Real.pi * t * Real.log m) : ℝ) * Complex.I)
  have he : ∀ m t, ‖e m t‖ = 1 := fun m t => Complex.norm_exp_ofReal_mul_I _
  have hrep' : ∀ m ∈ S, ∀ n ∈ S,
      cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * Complex.I) =
        ∫ t, e m t * e n t * φ t := by
    intro m hm n hn
    obtain ⟨hm1, hm2⟩ := log_window hN hm
    obtain ⟨hn1, hn2⟩ := log_window hN hn
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (lt_trans (by exact_mod_cast hN) (Finset.mem_Ioc.1 hm).1)
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (lt_trans (by exact_mod_cast hN) (Finset.mem_Ioc.1 hn).1)
    have h := hrep (Real.log m + Real.log n) (by simp only [a]; linarith) (by simp only [a]; linarith)
    rw [sepPhase, exp_half_log_add hm0 hn0] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [e]
    rw [← Complex.exp_add]
    congr 2
    push_cast; ring
  have hcomp : ∀ m n, Integrable fun t => e m t * e n t * φ t := fun m n => by
    refine hint.norm.mono' ((by simp only [e]; fun_prop : Continuous fun t => e m t * e n t).aestronglyMeasurable.mul
      hint.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_mul, he, he, one_mul, one_mul]
  -- interchange
  have hB : ∑ m ∈ S, ∑ n ∈ S, conj (α m) * α n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
      cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * Complex.I) =
      ∫ t, φ t * ∑ m ∈ S, ∑ n ∈ S, (conj (α m) * e m t) * (α n * e n t) *
        kloostermanSum c (m : ZMod c) (n : ZMod c) := by
    have h1 : ∀ m ∈ S, ∀ n ∈ S, conj (α m) * α n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
        cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * Complex.I) =
        ∫ t, conj (α m) * α n * kloostermanSum c (m : ZMod c) (n : ZMod c) * (e m t * e n t * φ t) := by
      intro m hm n hn
      rw [hrep' m hm n hn, integral_const_mul]
    rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => h1 m hm n hn,
      Finset.sum_congr rfl fun m _ => (integral_finsetSum S fun n _ => (hcomp m n).const_mul _).symm,
      ← integral_finsetSum S fun m _ => integrable_finsetSum S fun n _ => (hcomp m n).const_mul _]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have hptw : ∀ t, ‖φ t * ∑ m ∈ S, ∑ n ∈ S, (conj (α m) * e m t) * (α n * e n t) *
      kloostermanSum c (m : ZMod c) (n : ZMod c)‖ ≤
      ‖φ t‖ * (((N : ℝ) + c) * ∑ n ∈ S, ‖α n‖ ^ 2) := fun t => by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_bilinear_kloostermanSum_le c N (fun m => conj (α m) * e m t)
      (fun n => α n * e n t)).trans (le_of_eq ?_)
    simp only [norm_mul, Complex.norm_conj, he, mul_one]
    ring
  rw [hB]
  have hea : Real.exp (a / 2) = N := by
    simp only [a]; rw [show 2 * Real.log N / 2 = Real.log N by ring, Real.exp_log hN0]
  have hAabs : |A| = 2 * |θ| / c := by
    simp only [A]; rw [abs_div, abs_mul, abs_of_pos hc]; norm_num
  calc ‖∫ t, φ t * ∑ m ∈ S, ∑ n ∈ S, (conj (α m) * e m t) * (α n * e n t) *
        kloostermanSum c (m : ZMod c) (n : ZMod c)‖
      ≤ ∫ t, ‖φ t‖ * (((N : ℝ) + c) * ∑ n ∈ S, ‖α n‖ ^ 2) :=
        norm_integral_le_of_norm_le (hint.norm.mul_const _) (Eventually.of_forall hptw)
    _ = (∫ t, ‖φ t‖) * (((N : ℝ) + c) * ∑ n ∈ S, ‖α n‖ ^ 2) := integral_mul_const _ _
    _ ≤ C₀ * (1 + |A| * Real.exp (a / 2)) * (((N : ℝ) + c) * ∑ n ∈ S, ‖α n‖ ^ 2) := by
        gcongr
    _ ≤ 2 * C₀ * (1 + |θ| * N / c) * ((N : ℝ) + c) * ∑ n ∈ S, ‖α n‖ ^ 2 := by
        rw [hea, hAabs]
        have hS : 0 ≤ ((N : ℝ) + c) * ∑ n ∈ S, ‖α n‖ ^ 2 := by positivity
        have h1 : 1 + 2 * |θ| / c * N ≤ 2 * (1 + |θ| * N / c) := by
          have : 0 ≤ |θ| * N / c := by positivity
          rw [show 2 * |θ| / c * N = 2 * (|θ| * N / c) by ring]
          linarith
        calc C₀ * (1 + 2 * |θ| / c * N) * (((N : ℝ) + c) * ∑ n ∈ S, ‖α n‖ ^ 2)
            ≤ C₀ * (2 * (1 + |θ| * N / c)) * (((N : ℝ) + c) * ∑ n ∈ S, ‖α n‖ ^ 2) := by gcongr
          _ = _ := by ring

end

end GaloisForLFunctions.RHTower.KuznetsovSeparation
