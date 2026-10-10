import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley
import GaloisForLFunctions.RHTower.XiWindowZeroCount

/-!
# Off-line zeros have polynomially isolated real-part peaks

Fix `½ < σ₀ < 1`.  By the Ingham–Huxley density estimate, the zeros with `Re ρ ≥ σ₀` and
`T ≤ Im ρ ≤ 2T` number at most `D (1 + log T)^B T^e` with `e < 1`.  Hence there is `c > 0` such
that, above every large height, every zero with `Re ρ ≥ σ₀` leads to a zero `ρ*` with
`Re ρ* ≥ Re ρ` that is a **local maximum of the real part in the height window
`|Im ρ′ − Im ρ*| ≤ (Im ρ*)^c`** (`exists_isolated_rePeak`).

Proof.  Suppose not.  Then from `ρ` one can step repeatedly to a zero of strictly larger real part
within height `(Im)^c`.  Such a walk visits distinct zeros of real part `≥ σ₀`.  To leave a dyadic
height box `[T, 2T]`, whether downwards from its top or upwards from its bottom, it needs about
`T^{1−c}` consecutive steps inside the box.  That exceeds the box count `D (1+log T)^B T^e` once
`e + c < 1` and `T` is large.  So the walk can neither drop below the starting scale nor climb
forever.  Climbing forever is forced, since it visits infinitely many distinct zeros and only
finitely many zeros lie below any height.

This is the target selection used to attack an off-line chain from inside the JAS dressed
aggregate: a farthest zero exists inside polynomially wide height windows.
-/

open Complex Filter Topology Asymptotics

namespace RHTower

noncomputable section

/-! ## The density exponent is below one -/

theorem inghamHuxleyExponent_mul_lt_one {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ < 1) :
    inghamHuxleyExponent σ * (1 - σ) < 1 := by
  unfold inghamHuxleyExponent
  split_ifs with ha hb
  · have hpos : 0 < 2 - σ := by linarith
    rw [div_mul_eq_mul_div, div_lt_one hpos]; linarith
  · have hpos : 0 < 3 * σ - 1 := by linarith
    rw [div_mul_eq_mul_div, div_lt_one hpos]; push Not at ha; linarith
  · linarith

/-! ## An eventual inequality -/

theorem eventually_rpow_mul_count_lt {D e c : ℝ} {B : ℕ} (hc : 0 < c) (he : 0 ≤ e)
    (hec : e + c < 1) (hD : 0 ≤ D) :
    ∀ᶠ T in atTop, (4 * T) ^ c * (D * (1 + Real.log T) ^ B * T ^ e + 2) < T := by
  set s : ℝ := 1 - e - c with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have h1 : Tendsto (fun T : ℝ => Real.log T ^ (B : ℝ) / T ^ s) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (B : ℝ) hs0).tendsto_div_nhds_zero
  have h2 : Tendsto (fun T : ℝ => T ^ (-(1 - c))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  set K : ℝ := 4 ^ c * (D * 2 ^ B) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hε : (0 : ℝ) < 1 / (4 * (K + 1)) := by positivity
  have hε2 : (0 : ℝ) < 1 / (4 * (4 ^ c * 2 + 1)) := by positivity
  filter_upwards [h1.eventually (gt_mem_nhds hε), h2.eventually (gt_mem_nhds hε2),
    eventually_ge_atTop (Real.exp 1)] with T hT1 hT2 hTe
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hTe
  have hlog1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hTe
  have hlogB : (1 + Real.log T) ^ B ≤ 2 ^ B * Real.log T ^ (B : ℝ) := by
    rw [Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) B
  have hTs : 0 < T ^ s := Real.rpow_pos_of_pos hT0 s
  have hlogs : Real.log T ^ (B : ℝ) < 1 / (4 * (K + 1)) * T ^ s := by
    rwa [div_lt_iff₀ hTs] at hT1
  -- `(4T)^c T^e (log T)^B ≤ T / 4`
  have h4c : (4 * T) ^ c = 4 ^ c * T ^ c := Real.mul_rpow (by norm_num) hT0.le
  have hTce : T ^ c * T ^ e * T ^ s = T := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, hs]
    ring_nf
    exact Real.rpow_one T
  have hA : (4 * T) ^ c * (D * (1 + Real.log T) ^ B * T ^ e) ≤ T / 4 := by
    rw [h4c]
    have hTc0 : 0 ≤ T ^ c := (Real.rpow_pos_of_pos hT0 c).le
    have hTe0 : 0 ≤ T ^ e := (Real.rpow_pos_of_pos hT0 e).le
    calc 4 ^ c * T ^ c * (D * (1 + Real.log T) ^ B * T ^ e)
        ≤ 4 ^ c * T ^ c * (D * (2 ^ B * Real.log T ^ (B : ℝ)) * T ^ e) := by
          gcongr
      _ = K * (T ^ c * T ^ e) * Real.log T ^ (B : ℝ) := by rw [hK]; ring
      _ ≤ K * (T ^ c * T ^ e) * (1 / (4 * (K + 1)) * T ^ s) := by
          gcongr
      _ = K / (4 * (K + 1)) * (T ^ c * T ^ e * T ^ s) := by ring
      _ = K / (4 * (K + 1)) * T := by rw [hTce]
      _ ≤ T / 4 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hB : (4 * T) ^ c * 2 < T / 2 := by
    rw [h4c]
    set u := T ^ (-(1 - c)) with hu
    have hlt : u < 1 / (4 * ((4 : ℝ) ^ c * 2 + 1)) := hT2
    have hrel : T ^ c = T * u := by
      rw [hu, ← Real.rpow_one_add' hT0.le (by linarith)]; ring_nf
    have h4 : (0 : ℝ) < (4 : ℝ) ^ c := by positivity
    have hu0 : 0 ≤ u := (Real.rpow_pos_of_pos hT0 _).le
    have hq : (4 : ℝ) ^ c * 2 * u < 1 / 2 := by
      have e1 : (4 : ℝ) ^ c * 2 * (1 / (4 * ((4 : ℝ) ^ c * 2 + 1))) =
          (4 : ℝ) ^ c * 2 / (4 * ((4 : ℝ) ^ c * 2 + 1)) := by ring
      have h5 : (4 : ℝ) ^ c * 2 / (4 * ((4 : ℝ) ^ c * 2 + 1)) < 1 / 2 := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith
      calc (4 : ℝ) ^ c * 2 * u < (4 : ℝ) ^ c * 2 * (1 / (4 * ((4 : ℝ) ^ c * 2 + 1))) :=
            mul_lt_mul_of_pos_left hlt (by positivity)
        _ < 1 / 2 := by rw [e1]; exact h5
    rw [hrel, show (4 : ℝ) ^ c * (T * u) * 2 = T * ((4 : ℝ) ^ c * 2 * u) by ring]
    have := mul_lt_mul_of_pos_left hq hT0
    linarith
  rw [mul_add]
  linarith

/-! ## Crossing a box costs many distinct zeros -/

theorem abs_im_sub_le_mul_ncard {σ T L : ℝ} (hL : 0 ≤ L) (s : ℕ → XiZeroCopy) {a b : ℕ}
    (hab : a ≤ b) (hbox : ∀ k, a ≤ k → k ≤ b → s k ∈ zeroHeightBox σ T)
    (hstep : ∀ k, a ≤ k → k < b → |((s (k + 1)).1 : ℂ).im - ((s k).1 : ℂ).im| ≤ L)
    (hinj : ∀ i j, a ≤ i → i ≤ b → a ≤ j → j ≤ b → s i = s j → i = j) :
    |((s b).1 : ℂ).im - ((s a).1 : ℂ).im| ≤ L * ((zeroHeightBox σ T).ncard : ℝ) := by
  classical
  -- telescoping
  have htel : ∀ m, a + m ≤ b →
      |((s (a + m)).1 : ℂ).im - ((s a).1 : ℂ).im| ≤ L * m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := hstep (a + m) (by omega) (by omega)
      rw [show a + (m + 1) = a + m + 1 by ring]
      calc |((s (a + m + 1)).1 : ℂ).im - ((s a).1 : ℂ).im|
          ≤ |((s (a + m + 1)).1 : ℂ).im - ((s (a + m)).1 : ℂ).im| +
            |((s (a + m)).1 : ℂ).im - ((s a).1 : ℂ).im| := abs_sub_le _ _ _
        _ ≤ L + L * m := add_le_add h2 h1
        _ = L * ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hmain := htel (b - a) (by omega)
  rw [show a + (b - a) = b by omega] at hmain
  -- counting
  have hfin := zeroHeightBox_finite σ T
  have hsub : (Finset.Icc a b).image s ⊆ hfin.toFinset := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    exact hfin.mem_toFinset.mpr (hbox k hk1 hk2)
  have hcard : ((Finset.Icc a b).image s).card = b - a + 1 := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro i hi j hj h
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
      exact hinj i j hi1 hi2 hj1 hj2 h
  have hle : b - a + 1 ≤ (zeroHeightBox σ T).ncard := by
    rw [← hcard, Set.ncard_eq_toFinset_card _ hfin]
    exact Finset.card_le_card hsub
  have hle' : ((b - a : ℕ) : ℝ) ≤ (zeroHeightBox σ T).ncard := by
    exact_mod_cast (show b - a ≤ (zeroHeightBox σ T).ncard by omega)
  exact hmain.trans (mul_le_mul_of_nonneg_left hle' hL)

/-! ## The main theorem -/

/-- `x^c ≤ x/2` for large `x`. -/
theorem eventually_rpow_le_half {c : ℝ} (hc0 : 0 < c) (hc : c < 1) :
    ∀ᶠ x : ℝ in atTop, x ^ c ≤ x / 2 := by
  have h := tendsto_rpow_neg_atTop (show 0 < 1 - c by linarith)
  filter_upwards [h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_gt_atTop 0] with x hx hx0
  have hrel : x ^ c = x * x ^ (-(1 - c)) := by
    rw [← Real.rpow_one_add' hx0.le (by linarith)]; ring_nf
  rw [hrel]
  have := mul_le_mul_of_nonneg_left hx hx0.le
  linarith

/-- **Polynomially isolated real-part peaks.**  For `½ < σ₀ < 1` there are `0 < c < 1` and `G₀`
such that above every height `G ≥ G₀` every zero `q₀` with `Re q₀ ≥ σ₀`, `Im q₀ ≥ 2G` leads to a
zero `q` with `Re q ≥ Re q₀`, `Im q ≥ G`, and `Re q′ ≤ Re q` for every zero `q′` with
`|Im q′ − Im q| ≤ (Im q)^c`. -/
theorem exists_isolated_rePeak {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) (hσ₁ : σ₀ < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ G₀ : ℝ, 1 ≤ G₀ ∧ ∀ G : ℝ, G₀ ≤ G →
      ∀ q₀ : XiZeroCopy, σ₀ ≤ ((q₀.1 : ℂ)).re → 2 * G ≤ ((q₀.1 : ℂ)).im →
        ∃ q : XiZeroCopy, ((q₀.1 : ℂ)).re ≤ ((q.1 : ℂ)).re ∧ G ≤ ((q.1 : ℂ)).im ∧
          ∀ q' : XiZeroCopy, |((q'.1 : ℂ)).im - ((q.1 : ℂ)).im| ≤ ((q.1 : ℂ)).im ^ c →
            ((q'.1 : ℂ)).re ≤ ((q.1 : ℂ)).re := by
  classical
  set A := inghamHuxleyExponent σ₀ with hA
  have hA1 := inghamHuxleyExponent_mul_lt_one hσ₀ hσ₁
  have hA0 : 0 < A := by
    rw [hA]; unfold inghamHuxleyExponent; split_ifs <;> first | positivity | (apply div_pos <;> linarith)
  set ε : ℝ := min 1 ((1 / (1 - σ₀) - A) / 2) with hεdef
  have h1σ : 0 < 1 - σ₀ := by linarith
  have hgap : 0 < 1 / (1 - σ₀) - A := by
    rw [sub_pos, lt_div_iff₀ h1σ]; linarith
  have hε0 : 0 < ε := lt_min one_pos (by linarith)
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨D, hD, B, T₀, hT₀, hdens⟩ := exists_zeroHeightBox_ncard_le_ingham_huxley hσ₀ hσ₁.le hε0 hε1
  set e : ℝ := (A + ε) * (1 - σ₀) with he
  have he0 : 0 ≤ e := by rw [he]; positivity
  have he1 : e < 1 := by
    have : ε ≤ (1 / (1 - σ₀) - A) / 2 := min_le_right _ _
    have h2 : (A + ε) * (1 - σ₀) ≤ (A + (1 / (1 - σ₀) - A) / 2) * (1 - σ₀) :=
      mul_le_mul_of_nonneg_right (by linarith) h1σ.le
    have h3 : (A + (1 / (1 - σ₀) - A) / 2) * (1 - σ₀) = (A * (1 - σ₀) + 1) / 2 := by
      field_simp; ring
    rw [he]; linarith
  set c : ℝ := (1 - e) / 4 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  have hec : e + c < 1 := by rw [hc]; linarith
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_rpow_mul_count_lt hc0 he0 hec hD (B := B))
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (eventually_rpow_le_half hc0 hc1)
  set G₀ : ℝ := max (max 1 T₀) (max T₂ X₁) with hG₀
  refine ⟨c, hc0, hc1, G₀, le_max_of_le_left (le_max_left _ _), ?_⟩
  -- the crossing contradiction at any scale `T ≥ G₀`
  have hcross : ∀ T : ℝ, G₀ ≤ T → ∀ (s : ℕ → XiZeroCopy) (a b : ℕ), a ≤ b →
      (∀ k, a ≤ k → k ≤ b → s k ∈ zeroHeightBox σ₀ T) →
      (∀ k, a ≤ k → k < b → |((s (k + 1)).1 : ℂ).im - ((s k).1 : ℂ).im| ≤ (4 * T) ^ c) →
      (∀ i j, a ≤ i → i ≤ b → a ≤ j → j ≤ b → s i = s j → i = j) →
      T - 2 * (4 * T) ^ c < |((s b).1 : ℂ).im - ((s a).1 : ℂ).im| → False := by
    intro T hT s a b hab hbox hstep hinj hbig
    have hT1 : 1 ≤ T := le_trans (le_max_of_le_left (le_max_left _ _)) hT
    have hTT₀ : T₀ ≤ T := le_trans (le_max_of_le_left (le_max_right _ _)) hT
    have hTT₂ : T₂ ≤ T := le_trans (le_max_of_le_right (le_max_left _ _)) hT
    have hL : 0 ≤ (4 * T) ^ c := (Real.rpow_pos_of_pos (by linarith) c).le
    have hcnt := abs_im_sub_le_mul_ncard hL s hab hbox hstep hinj
    have hd := hdens T hTT₀
    have hineq := hT₂ T hTT₂
    have h4 : (4 * T) ^ c * ((zeroHeightBox σ₀ T).ncard : ℝ) ≤
        (4 * T) ^ c * (D * (1 + Real.log T) ^ B * T ^ e) := mul_le_mul_of_nonneg_left hd hL
    nlinarith
  intro G hG q₀ hq₀re hq₀im
  have hG1 : 1 ≤ G := le_trans (le_max_of_le_left (le_max_left _ _)) hG
  have hG0 : 0 < G := by linarith
  have hGX : X₁ ≤ G := le_trans (le_max_of_le_right (le_max_right _ _)) hG
  by_contra hneg
  push Not at hneg
  -- the walk
  set P : XiZeroCopy → Prop :=
    fun q => ((q₀.1 : ℂ)).re ≤ ((q.1 : ℂ)).re ∧ G ≤ ((q.1 : ℂ)).im with hPdef
  have hnext : ∀ q, P q → ∃ q' : XiZeroCopy,
      |((q'.1 : ℂ)).im - ((q.1 : ℂ)).im| ≤ ((q.1 : ℂ)).im ^ c ∧
        ((q.1 : ℂ)).re < ((q'.1 : ℂ)).re := fun q hq => hneg q hq.1 hq.2
  let nxt : XiZeroCopy → XiZeroCopy := fun q => if h : P q then (hnext q h).choose else q
  let w : ℕ → XiZeroCopy := fun k => nxt^[k] q₀
  have hw_succ : ∀ k, w (k + 1) = nxt (w k) := fun k => Function.iterate_succ_apply' nxt k q₀
  have hnxt_spec : ∀ q, P q → |((nxt q).1 : ℂ).im - ((q.1 : ℂ)).im| ≤ ((q.1 : ℂ)).im ^ c ∧
      ((q.1 : ℂ)).re < ((nxt q).1 : ℂ).re := by
    intro q hq
    simp only [nxt, dif_pos hq]
    exact (hnext q hq).choose_spec
  -- while the walk stays at height `≥ G`, it is a valid walk
  have hvalid : ∀ k, (∀ j ≤ k, G ≤ ((w j).1 : ℂ).im) → ∀ j ≤ k, P (w j) := by
    intro k hk j hj
    induction j with
    | zero => exact ⟨le_rfl, hk 0 (Nat.zero_le _)⟩
    | succ j ih =>
      have hPj := ih (by omega)
      refine ⟨?_, hk (j + 1) hj⟩
      rw [hw_succ]
      exact le_trans hPj.1 (hnxt_spec _ hPj).2.le
  have hmono : ∀ k, (∀ j ≤ k, G ≤ ((w j).1 : ℂ).im) → ∀ i j, i < j → j ≤ k →
      ((w i).1 : ℂ).re < ((w j).1 : ℂ).re := by
    intro k hk i j hij hjk
    induction j with
    | zero => omega
    | succ j ih =>
      have hPj := hvalid k hk j (by omega)
      have hstep := (hnxt_spec _ hPj).2
      rw [hw_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h (by omega)) hstep
      · rw [h]; exact hstep
  have hinjw : ∀ k, (∀ j ≤ k, G ≤ ((w j).1 : ℂ).im) → ∀ i j, i ≤ k → j ≤ k → w i = w j →
      i = j := by
    intro k hk i j hi hj h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hmono k hk i j hlt hj; rw [h] at this; exact lt_irrefl _ this
    · have := hmono k hk j i hlt hi; rw [h] at this; exact lt_irrefl _ this
  have hstep_w : ∀ k, (∀ j ≤ k, G ≤ ((w j).1 : ℂ).im) →
      |((w (k + 1)).1 : ℂ).im - ((w k).1 : ℂ).im| ≤ ((w k).1 : ℂ).im ^ c := by
    intro k hk
    rw [hw_succ]
    exact (hnxt_spec _ (hvalid k hk k le_rfl)).1
  have hrpow_mono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → x ^ c ≤ y ^ c := fun x y hx hxy =>
    Real.rpow_le_rpow hx hxy hc0.le
  -- Step 1: the walk never drops below `G`
  have hstay : ∀ k, G ≤ ((w k).1 : ℂ).im := by
    by_contra hdrop
    push Not at hdrop
    obtain ⟨k₁, hk₁⟩ := hdrop
    let k₁' := Nat.find (⟨k₁, hk₁⟩ : ∃ k, ((w k).1 : ℂ).im < G)
    have hk₁'spec : ((w k₁').1 : ℂ).im < G := Nat.find_spec (⟨k₁, hk₁⟩ : ∃ k, ((w k).1 : ℂ).im < G)
    have hbefore : ∀ j < k₁', G ≤ ((w j).1 : ℂ).im := fun j hj => by
      have := Nat.find_min (⟨k₁, hk₁⟩ : ∃ k, ((w k).1 : ℂ).im < G) hj
      push Not at this; exact this
    have hk₁pos : 0 < k₁' := by
      by_contra h0; push Not at h0
      have : k₁' = 0 := by omega
      rw [this] at hk₁'spec
      simp only [w, Function.iterate_zero, id] at hk₁'spec
      linarith
    set m := k₁' - 1 with hm
    have hm1 : m + 1 = k₁' := by omega
    have hall : ∀ j ≤ m, G ≤ ((w j).1 : ℂ).im := fun j hj => hbefore j (by omega)
    -- last index with height `≥ 2G`
    let i := Nat.findGreatest (fun j => 2 * G ≤ ((w j).1 : ℂ).im) m
    have hi_spec : 2 * G ≤ ((w i).1 : ℂ).im :=
      Nat.findGreatest_spec (P := fun j => 2 * G ≤ ((w j).1 : ℂ).im) (Nat.zero_le m)
        (by simp only [w, Function.iterate_zero, id]; exact hq₀im)
    have hi_le : i ≤ m := Nat.findGreatest_le m
    have hi_after : ∀ j, i < j → j ≤ m → ((w j).1 : ℂ).im < 2 * G := by
      intro j hij hjm
      have := Nat.findGreatest_is_greatest (P := fun j => 2 * G ≤ ((w j).1 : ℂ).im) hij hjm
      push Not at this; exact this
    -- the exit step: `Im w m < G + (2G)^c`
    have hexit : ((w m).1 : ℂ).im < G + (4 * G) ^ c := by
      have hs := hstep_w m hall
      rw [hm1] at hs
      have hb : ((w m).1 : ℂ).im ^ c ≤ (4 * G) ^ c := by
        rcases eq_or_lt_of_le hi_le with heq | hlt
        · -- `i = m`: the step from `≥ 2G` lands below `G`, impossible
          exfalso
          have h2 : 2 * G ≤ ((w m).1 : ℂ).im := heq ▸ hi_spec
          have hX : X₁ ≤ ((w m).1 : ℂ).im := by linarith
          have hhalf := hX₁ _ hX
          rw [abs_le] at hs
          linarith
        · have hlt2 := hi_after m hlt le_rfl
          exact hrpow_mono _ _ (by linarith [hall m le_rfl]) (by linarith)
      rw [abs_le] at hs
      linarith
    rcases eq_or_lt_of_le hi_le with heq | hlt
    · -- `i = m`: impossible, the step from `≥ 2G` cannot land below `G`
      have h2 : 2 * G ≤ ((w m).1 : ℂ).im := heq ▸ hi_spec
      have hs := hstep_w m hall
      rw [hm1] at hs
      have hhalf := hX₁ (((w m).1 : ℂ).im) (by linarith)
      rw [abs_le] at hs
      linarith
    · -- in-box indices `i+1 … m`
      have hentry_lo : 2 * G - (4 * G) ^ c ≤ ((w (i + 1)).1 : ℂ).im := by
        have hs := hstep_w i (fun j hj => hall j (by omega))
        have hbox_hi := hi_after (i + 1) (by omega) (by omega)
        -- `Im w i < 4G`, else the step would land above `2G`
        have hlt4 : ((w i).1 : ℂ).im < 4 * G := by
          by_contra hge; push Not at hge
          have hhalf := hX₁ (((w i).1 : ℂ).im) (by linarith)
          rw [abs_le] at hs
          linarith
        have hb : ((w i).1 : ℂ).im ^ c ≤ (4 * G) ^ c :=
          hrpow_mono _ _ (by linarith [hall i hi_le]) hlt4.le
        rw [abs_le] at hs
        linarith
      refine hcross G (le_refl _ |>.trans' hG) w (i + 1) m (by omega) ?_ ?_ ?_ ?_
      · intro k hk1 hk2
        exact ⟨le_trans hq₀re (hvalid m hall k hk2).1, hall k hk2,
          (hi_after k (by omega) hk2).le⟩
      · intro k hk1 hk2
        have hs := hstep_w k (fun j hj => hall j (by omega))
        have hb : ((w k).1 : ℂ).im ^ c ≤ (4 * G) ^ c :=
          hrpow_mono _ _ (by linarith [hall k (by omega)])
            (by linarith [hi_after k (by omega) (by omega)])
        linarith
      · intro i' j' hi1 hi2 hj1 hj2 h
        exact hinjw m hall i' j' hi2 hj2 h
      · calc G - 2 * (4 * G) ^ c < ((w (i + 1)).1 : ℂ).im - ((w m).1 : ℂ).im := by linarith
          _ ≤ |((w m).1 : ℂ).im - ((w (i + 1)).1 : ℂ).im| := by
            rw [abs_sub_comm]; exact le_abs_self _
  -- Step 2: the walk is injective, hence unbounded in height
  have hinj_all : ∀ i j, w i = w j → i = j := fun i j h =>
    hinjw (max i j) (fun l _ => hstay l) i j (le_max_left _ _) (le_max_right _ _) h
  set T : ℝ := max G₀ (((w 0).1 : ℂ).im + 1) with hTdef
  have hTG₀ : G₀ ≤ T := le_max_left _ _
  have hT1 : 1 ≤ T := le_trans (le_max_of_le_left (le_max_left _ _)) hTG₀
  have hT0lt : ((w 0).1 : ℂ).im < T := by
    have := le_max_right G₀ (((w 0).1 : ℂ).im + 1); linarith
  have hTX : X₁ ≤ T := le_trans (le_max_of_le_right (le_max_right _ _)) hTG₀
  have hup : ∃ k, 2 * T < ((w k).1 : ℂ).im := by
    by_contra hbd
    push Not at hbd
    -- all `w k` lie in a bounded window: impossible for an injective sequence
    have hfin := finite_xiOrdinateWindow (2 * T) 0
    have hmem : ∀ k, w k ∈ xiOrdinateWindow (2 * T) 0 := by
      intro k
      show |((w k).1 : ℂ).im - 0| ≤ 2 * T
      rw [sub_zero, abs_le]
      exact ⟨by linarith [hstay k], hbd k⟩
    exact Set.infinite_of_injective_forall_mem (fun i j h => hinj_all i j h) hmem hfin
  let k₂ := Nat.find hup
  have hk₂spec : 2 * T < ((w k₂).1 : ℂ).im := Nat.find_spec hup
  have hk₂min : ∀ j < k₂, ((w j).1 : ℂ).im ≤ 2 * T := fun j hj => by
    have := Nat.find_min hup hj; push Not at this; exact this
  have hk₂pos : 0 < k₂ := by
    by_contra h0; push Not at h0
    have : k₂ = 0 := by omega
    rw [this] at hk₂spec; linarith
  set m := k₂ - 1 with hm
  have hm1 : m + 1 = k₂ := by omega
  let i := Nat.findGreatest (fun j => ((w j).1 : ℂ).im < T) m
  have hi_spec : ((w i).1 : ℂ).im < T :=
    Nat.findGreatest_spec (P := fun j => ((w j).1 : ℂ).im < T) (Nat.zero_le m) hT0lt
  have hi_le : i ≤ m := Nat.findGreatest_le m
  have hi_after : ∀ j, i < j → j ≤ m → T ≤ ((w j).1 : ℂ).im := by
    intro j hij hjm
    have := Nat.findGreatest_is_greatest (P := fun j => ((w j).1 : ℂ).im < T) hij hjm
    push Not at this; exact this
  have hrpow_le_self : ∀ x : ℝ, 1 ≤ x → x ^ c ≤ x := fun x hx =>
    by simpa using Real.rpow_le_rpow_of_exponent_le hx hc1.le
  rcases eq_or_lt_of_le hi_le with heq | hlt
  · -- one step from below `T` to above `2T`
    have hs := hstep_w m (fun l _ => hstay l)
    rw [hm1] at hs
    have hwm : ((w m).1 : ℂ).im < T := heq ▸ hi_spec
    have hb : ((w m).1 : ℂ).im ^ c ≤ ((w m).1 : ℂ).im :=
      hrpow_le_self _ (by linarith [hstay m])
    rw [abs_le] at hs
    linarith
  · have hexit : 2 * T - (4 * T) ^ c < ((w m).1 : ℂ).im := by
      have hs := hstep_w m (fun l _ => hstay l)
      rw [hm1] at hs
      have hb : ((w m).1 : ℂ).im ^ c ≤ (4 * T) ^ c :=
        hrpow_mono _ _ (by linarith [hstay m]) (by linarith [hk₂min m (by omega)])
      rw [abs_le] at hs
      linarith
    have hentry : ((w (i + 1)).1 : ℂ).im < T + (4 * T) ^ c := by
      have hs := hstep_w i (fun l _ => hstay l)
      have hb : ((w i).1 : ℂ).im ^ c ≤ (4 * T) ^ c :=
        hrpow_mono _ _ (by linarith [hstay i]) (by linarith)
      rw [abs_le] at hs
      linarith
    refine hcross T hTG₀ w (i + 1) m (by omega) ?_ ?_ ?_ ?_
    · intro k hk1 hk2
      exact ⟨le_trans hq₀re (hvalid k (fun l _ => hstay l) k le_rfl).1,
        hi_after k (by omega) hk2, hk₂min k (by omega)⟩
    · intro k hk1 hk2
      have hs := hstep_w k (fun l _ => hstay l)
      have hb : ((w k).1 : ℂ).im ^ c ≤ (4 * T) ^ c :=
        hrpow_mono _ _ (by linarith [hstay k]) (by linarith [hk₂min k (by omega)])
      linarith
    · intro i' j' _ _ _ _ h
      exact hinj_all i' j' h
    · calc T - 2 * (4 * T) ^ c < ((w m).1 : ℂ).im - ((w (i + 1)).1 : ℂ).im := by linarith
        _ ≤ |((w m).1 : ℂ).im - ((w (i + 1)).1 : ℂ).im| := le_abs_self _

end

end RHTower
