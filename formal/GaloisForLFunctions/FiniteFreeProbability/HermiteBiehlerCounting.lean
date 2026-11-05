import Mathlib

/-!
# Counting real zeros by winding

Let `E` be a complex polynomial with real leading coefficient, with `Z₋` roots in the open lower
half-plane and `Z₊` in the open upper half-plane.

**Theorem.** `Re E` has at least `Z₋ − Z₊` distinct real zeros.

On the real axis `E(x) = A(x) e^{iΘ(x)}` with `A` real and `Θ(x) = Σ_{Im e ≠ 0} arg(x − e)` continuous.
Each non-real root contributes a phase running from `±π` at `−∞` to `0` at `+∞`: so `Θ` runs from
`π(Z₋ − Z₊)` to `0`, and takes each of the `Z₋ − Z₊` values `π/2 + kπ`, where `Re E = A cos Θ = 0`.
This is the counting form of the Hermite–Biehler theorem; it needs no hypothesis on the other roots.
-/

open Filter Topology Complex Polynomial

namespace FiniteFreeProbability

noncomputable section

/-- The phase of `x − e`: `arg(x − e)` for non-real `e`, and `0` for real `e`. -/
def rootPhase (e : ℂ) (x : ℝ) : ℝ := if e.im = 0 then 0 else Complex.arg ((x : ℂ) - e)

/-- The real amplitude of `x − e`. -/
def rootAmplitude (e : ℂ) (x : ℝ) : ℝ := if e.im = 0 then x - e.re else ‖(x : ℂ) - e‖

/-- The limit of `rootPhase e` at `−∞`. -/
def rootPhaseLimit (e : ℂ) : ℝ :=
  if e.im = 0 then 0 else if e.im < 0 then Real.pi else -Real.pi

theorem sub_eq_amplitude_mul_exp (e : ℂ) (x : ℝ) :
    (x : ℂ) - e = (rootAmplitude e x : ℂ) * Complex.exp ((rootPhase e x : ℂ) * I) := by
  unfold rootAmplitude rootPhase
  split_ifs with h
  · apply Complex.ext <;> simp [h]
  · exact (Complex.norm_mul_exp_arg_mul_I _).symm

theorem continuous_rootPhase (e : ℂ) : Continuous (rootPhase e) := by
  unfold rootPhase
  split_ifs with h
  · exact continuous_const
  · refine continuous_iff_continuousAt.2 fun x => ?_
    have hslit : (x : ℂ) - e ∈ Complex.slitPlane := by
      refine Or.inr ?_
      simpa using h
    exact ContinuousAt.comp (g := Complex.arg) (f := fun x : ℝ => (x : ℂ) - e)
      (Complex.continuousAt_arg hslit) (by fun_prop)

/-- `arg(x − e) → 0` as `x → +∞`. -/
theorem tendsto_arg_sub_atTop (e : ℂ) :
    Tendsto (fun x : ℝ => Complex.arg ((x : ℂ) - e)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (1 : ℂ) - e / (x : ℂ)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun x : ℝ => e / (x : ℂ)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (continuous_ofReal.tendsto _).comp tendsto_inv_atTop_zero
      have := hinv.const_mul e
      simpa [div_eq_mul_inv] using this
    simpa using h0.const_sub 1
  have harg : Tendsto (fun x : ℝ => Complex.arg ((1 : ℂ) - e / (x : ℂ))) atTop (𝓝 0) := by
    have hc := (Complex.continuousAt_arg (x := 1) (by simp)).tendsto.comp h1
    rw [Complex.arg_one] at hc
    exact hc
  refine harg.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  rw [show (x : ℂ) - e = (x : ℂ) * (1 - e / (x : ℂ)) by field_simp, Complex.arg_real_mul _ hx]

theorem tendsto_rootPhase_atTop (e : ℂ) : Tendsto (rootPhase e) atTop (𝓝 0) := by
  unfold rootPhase
  split_ifs with h
  · exact tendsto_const_nhds
  · exact tendsto_arg_sub_atTop e

theorem tendsto_rootPhase_atBot (e : ℂ) :
    Tendsto (rootPhase e) atBot (𝓝 (rootPhaseLimit e)) := by
  unfold rootPhase rootPhaseLimit
  by_cases h : e.im = 0
  · simp only [h, if_true]
    exact tendsto_const_nhds
  · simp only [h, if_false]
    have hg := (tendsto_arg_sub_atTop (-e)).comp tendsto_neg_atBot_atTop
    have himz : ∀ x : ℝ, (((-x : ℝ) : ℂ) - -e).im = e.im := fun x => by simp
    have hneg : ∀ x : ℝ, (x : ℂ) - e = -(((-x : ℝ) : ℂ) - -e) := fun x => by
      push_cast
      ring
    split_ifs with h2
    · have := hg.add_const Real.pi
      rw [zero_add] at this
      refine this.congr fun x => ?_
      simp only [Function.comp_apply]
      rw [hneg x, Complex.arg_neg_eq_arg_add_pi_of_im_neg (by rw [himz]; exact h2)]
    · have hpos : 0 < e.im := lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h)
      have := hg.sub_const Real.pi
      rw [zero_sub] at this
      refine this.congr fun x => ?_
      simp only [Function.comp_apply]
      rw [hneg x, Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by rw [himz]; exact hpos)]

/-- The total phase `Θ(x) = Σ_e rootPhase e x`. -/
def totalPhase (M : Multiset ℂ) (x : ℝ) : ℝ := (M.map fun e => rootPhase e x).sum

theorem totalPhase_zero : totalPhase 0 = fun _ => 0 := funext fun x => by simp [totalPhase]

theorem continuous_totalPhase (M : Multiset ℂ) : Continuous (totalPhase M) := by
  induction M using Multiset.induction_on with
  | empty =>
    rw [totalPhase_zero]
    exact continuous_const
  | cons a M ih =>
    have : totalPhase (a ::ₘ M) = fun x => rootPhase a x + totalPhase M x := by
      funext x
      simp [totalPhase]
    rw [this]
    exact (continuous_rootPhase a).add ih

theorem tendsto_totalPhase_atTop (M : Multiset ℂ) : Tendsto (totalPhase M) atTop (𝓝 0) := by
  induction M using Multiset.induction_on with
  | empty =>
    rw [totalPhase_zero]
    exact tendsto_const_nhds
  | cons a M ih =>
    have : totalPhase (a ::ₘ M) = fun x => rootPhase a x + totalPhase M x := by
      funext x
      simp [totalPhase]
    rw [this]
    simpa using (tendsto_rootPhase_atTop a).add ih

theorem tendsto_totalPhase_atBot (M : Multiset ℂ) :
    Tendsto (totalPhase M) atBot
      (𝓝 (Real.pi * ((Multiset.card (M.filter fun e => e.im < 0) : ℝ) -
        (Multiset.card (M.filter fun e => 0 < e.im) : ℝ)))) := by
  induction M using Multiset.induction_on with
  | empty =>
    rw [totalPhase_zero]
    simp
  | cons a M ih =>
    have hfun : totalPhase (a ::ₘ M) = fun x => rootPhase a x + totalPhase M x := by
      funext x
      simp [totalPhase]
    rw [hfun]
    have hsum := (tendsto_rootPhase_atBot a).add ih
    convert hsum using 2
    unfold rootPhaseLimit
    by_cases h : a.im = 0
    · have h1 : ¬ a.im < 0 := by rw [h]; exact lt_irrefl 0
      have h2 : ¬ 0 < a.im := by rw [h]; exact lt_irrefl 0
      rw [Multiset.filter_cons_of_neg (p := fun e => e.im < 0) M h1,
        Multiset.filter_cons_of_neg (p := fun e => 0 < e.im) M h2]
      simp [h]
    · by_cases h3 : a.im < 0
      · have h2 : ¬ 0 < a.im := not_lt.2 h3.le
        rw [Multiset.filter_cons_of_pos (p := fun e => e.im < 0) M h3,
          Multiset.filter_cons_of_neg (p := fun e => 0 < e.im) M h2, Multiset.card_cons]
        simp only [h, h3, if_true, if_false]
        push_cast
        ring
      · have h2 : 0 < a.im := lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h)
        rw [Multiset.filter_cons_of_neg (p := fun e => e.im < 0) M h3,
          Multiset.filter_cons_of_pos (p := fun e => 0 < e.im) M h2, Multiset.card_cons]
        simp only [h, h3, if_false]
        push_cast
        ring

theorem multiset_prod_sub_eq (M : Multiset ℂ) (x : ℝ) :
    (M.map fun e => (x : ℂ) - e).prod = (((M.map fun e => rootAmplitude e x).prod : ℝ) : ℂ) *
      Complex.exp ((totalPhase M x : ℂ) * I) := by
  induction M using Multiset.induction_on with
  | empty => simp [totalPhase]
  | cons a M ih =>
    have hphase : totalPhase (a ::ₘ M) x = rootPhase a x + totalPhase M x := by
      simp [totalPhase]
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, hphase]
    rw [sub_eq_amplitude_mul_exp a x]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring

/-- **Counting real zeros by winding.** If `E` has real leading coefficient, `Re E` has at least
`Z₋ − Z₊` distinct real zeros: `Z₋ ≤ |S| + Z₊`. -/
theorem exists_finset_re_eval_eq_zero (E : ℂ[X]) {a : ℝ} (ha : E.leadingCoeff = (a : ℂ)) :
    ∃ S : Finset ℝ, Multiset.card (E.roots.filter fun e => e.im < 0) ≤
        S.card + Multiset.card (E.roots.filter fun e => 0 < e.im) ∧
      ∀ x ∈ S, (E.eval (x : ℂ)).re = 0 := by
  set M := E.roots
  set Zm := Multiset.card (M.filter fun e => e.im < 0)
  set Zp := Multiset.card (M.filter fun e => 0 < e.im)
  set n := Zm - Zp
  have hn : (n : ℝ) ≥ (Zm : ℝ) - Zp := by
    have : Zm ≤ n + Zp := by omega
    have : (Zm : ℝ) ≤ n + Zp := by exact_mod_cast this
    linarith
  have hpi := Real.pi_pos
  set L : ℕ → ℝ := fun k => Real.pi / 2 + k * Real.pi
  have hL : ∀ k ∈ Finset.range n, ∃ x : ℝ, totalPhase M x = L k := fun k hk => by
    have hk' : k < n := Finset.mem_range.1 hk
    have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk'
    have hzmp : (Zm : ℝ) - Zp = n := by
      have hle : Zp ≤ Zm := by omega
      simp only [n]
      rw [Nat.cast_sub hle]
    have hLpos : 0 < L k := by
      simp only [L]
      positivity
    have hLlt : L k < Real.pi * ((Zm : ℝ) - Zp) := by
      rw [hzmp]
      simp only [L]
      nlinarith
    obtain ⟨b, hb⟩ := ((tendsto_totalPhase_atTop M).eventually (gt_mem_nhds hLpos)).exists
    obtain ⟨c, hc⟩ := ((tendsto_totalPhase_atBot M).eventually (lt_mem_nhds hLlt)).exists
    exact mem_range_of_exists_le_of_exists_ge (continuous_totalPhase M) ⟨b, hb.le⟩ ⟨c, hc.le⟩
  choose! x hx using hL
  have hinj : Set.InjOn x (Finset.range n : Set ℕ) := fun i hi j hj hij => by
    have h1 := hx i hi
    have h2 := hx j hj
    rw [hij, h2] at h1
    simp only [L] at h1
    have h3 : (j : ℝ) = i := by
      have := mul_right_cancel₀ hpi.ne' (add_left_cancel h1)
      exact this
    exact_mod_cast h3.symm
  refine ⟨(Finset.range n).image x, ?_, fun y hy => ?_⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    omega
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    have hval := hx k hk
    have heval : E.eval ((x k : ℝ) : ℂ) = (a : ℂ) * (((M.map fun e =>
        rootAmplitude e (x k)).prod : ℝ) : ℂ) * Complex.exp ((totalPhase M (x k) : ℂ) * I) := by
      conv_lhs => rw [(IsAlgClosed.splits E).eq_prod_roots]
      rw [eval_mul, eval_C, ha, eval_multiset_prod, Multiset.map_map]
      simp only [Function.comp_def, eval_sub, eval_X, eval_C]
      rw [multiset_prod_sub_eq, mul_assoc]
    have hcos : Real.cos (L k) = 0 := by
      rw [Real.cos_eq_zero_iff]
      refine ⟨k, ?_⟩
      simp only [L]
      push_cast
      ring
    rw [heval, ← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, hval, hcos,
      mul_zero]

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.exists_finset_re_eval_eq_zero
