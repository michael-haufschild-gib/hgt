import GaloisForLFunctions.LogarithmicChowla.LogarithmicAverages

/-!
# Limit functionals of logarithmic averages

For an ultrafilter `U ≤ atTop` on `ℝ` and a bounded `f : ℕ → ℝ`, the averages `A_x(f)` stay in a
compact interval, so they converge along `U`; `L_U(f) = lim_U A_x(f)` (`limAvg`). The functional is
linear, positive, normalised, and exactly

* shift invariant: `L(f(·+1)) = L(f)` (`limAvg_shift`);
* dilation covariant: `L(f(d·)) = L(d·1_{d|·} f)` (`limAvg_dilate`);
* uniform on residues: `L(1_{n ≡ r mod Q}) = 1/Q` (`limAvg_residue`), since the shift permutes the
  residue indicators cyclically.

A bounded `A_x(f)` tends to `0` once `L_U(f) = 0` for every `U ≤ atTop`
(`tendsto_logAvg_of_forall_limAvg_eq_zero`).

The law of a finite-valued `g : ℕ → α` is `a ↦ L(1_{g=a})` (`law`): a probability vector
(`sum_law`), pushed forward by functions (`law_comp`), and shift invariant (`law_shift`).
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Topology

noncomputable section

/-- A bounded sequence. -/
def Bdd (f : ℕ → ℝ) : Prop := ∃ B, ∀ n, |f n| ≤ B

theorem bdd_const (c : ℝ) : Bdd fun _ => c := ⟨|c|, fun _ => le_rfl⟩

theorem Bdd.add {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun n => f n + g n := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A + B, fun n => (abs_add_le _ _).trans (add_le_add (hA n) (hB n))⟩

theorem Bdd.mul {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun n => f n * g n := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨A * B, fun n => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hA n) (hB n) (abs_nonneg _) ((abs_nonneg _).trans (hA 0))

theorem Bdd.const_mul {f : ℕ → ℝ} (hf : Bdd f) (c : ℝ) : Bdd fun n => c * f n :=
  (bdd_const c).mul hf

theorem Bdd.neg {f : ℕ → ℝ} (hf : Bdd f) : Bdd fun n => -f n := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun n => by rw [abs_neg]; exact hA n⟩

theorem Bdd.sub {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd fun n => f n - g n := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem Bdd.comp_add {f : ℕ → ℝ} (hf : Bdd f) (m : ℕ) : Bdd fun n => f (n + m) := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun n => hA _⟩

theorem Bdd.comp_mul {f : ℕ → ℝ} (hf : Bdd f) (d : ℕ) : Bdd fun n => f (d * n) := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun n => hA _⟩

theorem bdd_sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ} (hf : ∀ i ∈ s, Bdd (f i)) :
    Bdd fun n => ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bdd_const 0
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem bdd_ite {p : ℕ → Prop} [DecidablePred p] {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) :
    Bdd fun n => if p n then f n else g n := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨max A B, fun n => ?_⟩
  show |if p n then f n else g n| ≤ max A B
  split_ifs
  · exact (hA n).trans (le_max_left _ _)
  · exact (hB n).trans (le_max_right _ _)

theorem bdd_indicator (p : ℕ → Prop) [DecidablePred p] : Bdd fun n => if p n then 1 else 0 :=
  bdd_ite (bdd_const 1) (bdd_const 0)

theorem Bdd.dvdWeight {f : ℕ → ℝ} (hf : Bdd f) (d : ℕ) :
    Bdd fun m => if d ∣ m then (d : ℝ) * f m else 0 :=
  bdd_ite (hf.const_mul _) (bdd_const 0)

/-- `L_U(f) = lim_U A_x(f)`. -/
def limAvg (U : Ultrafilter ℝ) (f : ℕ → ℝ) : ℝ := limUnder (U : Filter ℝ) (logAvg f)

variable {U : Ultrafilter ℝ}

theorem tendsto_limAvg (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} (hf : Bdd f) :
    Tendsto (logAvg f) U (𝓝 (limAvg U f)) := by
  obtain ⟨B, hB⟩ := hf
  refine tendsto_nhds_limUnder ?_
  have hev : ∀ᶠ x in (U : Filter ℝ), logAvg f x ∈ Set.Icc (-(2 * B)) (2 * B) :=
    hU ((eventually_ge_atTop (Real.exp 1)).mono fun x hx => abs_le.mp (abs_logAvg_le hB hx))
  have hle : ↑(Ultrafilter.map (logAvg f) U) ≤ 𝓟 (Set.Icc (-(2 * B)) (2 * B)) := by
    rw [Ultrafilter.coe_map, le_principal_iff]
    exact hev
  obtain ⟨a, -, ha⟩ := isCompact_Icc.ultrafilter_le_nhds _ hle
  exact ⟨a, by rwa [Ultrafilter.coe_map] at ha⟩

theorem limAvg_eq_of_tendsto (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} (hf : Bdd f) {a : ℝ}
    (h : Tendsto (logAvg f) U (𝓝 a)) : limAvg U f = a :=
  tendsto_nhds_unique (tendsto_limAvg hU hf) h

/-- Two sequences whose averages differ by `o(1)` along `atTop` have the same limit. -/
theorem limAvg_eq_of_sub (hU : (U : Filter ℝ) ≤ atTop) {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g)
    (h : Tendsto (fun x => logAvg f x - logAvg g x) atTop (𝓝 0)) : limAvg U f = limAvg U g := by
  have h1 : Tendsto (fun x => logAvg g x + (logAvg f x - logAvg g x)) U
      (𝓝 (limAvg U g + 0)) := (tendsto_limAvg hU hg).add (h.mono_left hU)
  simp only [add_sub_cancel, add_zero] at h1
  exact limAvg_eq_of_tendsto hU hf h1

theorem limAvg_add (hU : (U : Filter ℝ) ≤ atTop) {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) :
    limAvg U (fun n => f n + g n) = limAvg U f + limAvg U g := by
  refine limAvg_eq_of_tendsto hU (hf.add hg) ?_
  have h := (tendsto_limAvg hU hf).add (tendsto_limAvg hU hg)
  refine h.congr fun x => ?_
  simp only [logAvg, logSum_add, add_div]

theorem limAvg_const_mul (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} (hf : Bdd f) (c : ℝ) :
    limAvg U (fun n => c * f n) = c * limAvg U f := by
  refine limAvg_eq_of_tendsto hU (hf.const_mul c) ?_
  refine ((tendsto_limAvg hU hf).const_mul c).congr fun x => ?_
  simp only [logAvg, logSum_smul, mul_div_assoc]

theorem limAvg_neg (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} (hf : Bdd f) :
    limAvg U (fun n => -f n) = -limAvg U f := by
  have h := limAvg_const_mul hU hf (-1)
  simpa using h

theorem limAvg_sub (hU : (U : Filter ℝ) ≤ atTop) {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) :
    limAvg U (fun n => f n - g n) = limAvg U f - limAvg U g := by
  have h := limAvg_add hU hf hg.neg
  rw [limAvg_neg hU hg] at h
  simpa [sub_eq_add_neg] using h

theorem limAvg_sum (hU : (U : Filter ℝ) ≤ atTop) {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ}
    (hf : ∀ i ∈ s, Bdd (f i)) :
    limAvg U (fun n => ∑ i ∈ s, f i n) = ∑ i ∈ s, limAvg U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (fun n => ∑ i ∈ (∅ : Finset ι), f i n) = fun _ => 0 := by
      funext n
      simp
    rw [h0, sum_empty]
    refine limAvg_eq_of_tendsto hU (bdd_const 0) ?_
    have hz : logAvg (fun _ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      simp only [logAvg, logSum, zero_div, sum_const_zero]
    rw [hz]
    exact tendsto_const_nhds
  | insert a s ha ih =>
    simp only [sum_insert ha]
    rw [limAvg_add hU (hf a (mem_insert_self a s)) (bdd_sum s fun i hi => hf i
      (mem_insert_of_mem hi)), ih fun i hi => hf i (mem_insert_of_mem hi)]

theorem limAvg_const (hU : (U : Filter ℝ) ≤ atTop) (c : ℝ) : limAvg U (fun _ => c) = c := by
  refine limAvg_eq_of_tendsto hU (bdd_const c) ?_
  have h := (tendsto_logAvg_one.const_mul c).mono_left hU
  rw [mul_one] at h
  refine h.congr fun x => ?_
  have hc : (fun _ : ℕ => c) = fun n => c * (fun _ : ℕ => (1 : ℝ)) n := by
    funext n
    simp
  rw [hc, logAvg, logAvg, logSum_smul, mul_div_assoc]

theorem limAvg_mono (hU : (U : Filter ℝ) ≤ atTop) {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g)
    (h : ∀ n, f n ≤ g n) : limAvg U f ≤ limAvg U g := by
  refine le_of_tendsto_of_tendsto (tendsto_limAvg hU hf) (tendsto_limAvg hU hg) ?_
  refine hU ((eventually_gt_atTop (1 : ℝ)).mono fun x hx => ?_)
  exact div_le_div_of_nonneg_right (logSum_mono h _) (Real.log_pos hx).le

theorem limAvg_nonneg (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} (hf : Bdd f)
    (h : ∀ n, 0 ≤ f n) : 0 ≤ limAvg U f := by
  have := limAvg_mono hU (bdd_const 0) hf h
  rwa [limAvg_const hU] at this

theorem abs_limAvg_le (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} {B : ℝ} (hf : ∀ n, |f n| ≤ B) :
    |limAvg U f| ≤ B := by
  have hb : Bdd f := ⟨B, hf⟩
  have h1 := limAvg_mono hU hb (bdd_const B) fun n => (abs_le.mp (hf n)).2
  have h2 := limAvg_mono hU (bdd_const (-B)) hb fun n => (abs_le.mp (hf n)).1
  rw [limAvg_const hU] at h1 h2
  exact abs_le.mpr ⟨h2, h1⟩

/-- **Shift invariance.** `L(f(·+1)) = L(f)`. -/
theorem limAvg_shift (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} (hf : Bdd f) :
    limAvg U (fun n => f (n + 1)) = limAvg U f := by
  obtain ⟨B, hB⟩ := hf
  refine limAvg_eq_of_sub hU (Bdd.comp_add ⟨B, hB⟩ 1) ⟨B, hB⟩ ?_
  have hlim : Tendsto (fun x => 3 * B * (Real.log x)⁻¹) atTop (𝓝 0) := by
    simpa using (Real.tendsto_log_atTop.inv_tendsto_atTop).const_mul (3 * B)
  refine squeeze_zero_norm' (a := fun x => 3 * B * (Real.log x)⁻¹) ?_ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, ← div_eq_mul_inv]
  exact abs_logAvg_shift_sub_le hB hx

/-- `L(f(·+m)) = L(f)`. -/
theorem limAvg_shift_add (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} (hf : Bdd f) (m : ℕ) :
    limAvg U (fun n => f (n + m)) = limAvg U f := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := limAvg_shift hU (hf.comp_add m)
    simp only [Nat.add_assoc, Nat.add_comm 1 m] at h
    rw [← ih, ← h]

/-- **Dilation.** `L(f(d·)) = L(d·1_{d|·} f)`. -/
theorem limAvg_dilate (hU : (U : Filter ℝ) ≤ atTop) {f : ℕ → ℝ} (hf : Bdd f) {d : ℕ}
    (hd : 0 < d) :
    limAvg U (fun n => f (d * n)) = limAvg U (fun m => if d ∣ m then (d : ℝ) * f m else 0) := by
  obtain ⟨B, hB⟩ := hf
  refine limAvg_eq_of_sub hU (Bdd.comp_mul ⟨B, hB⟩ d) (Bdd.dvdWeight ⟨B, hB⟩ d) ?_
  have hlim : Tendsto (fun x => d * B * (Real.log x)⁻¹) atTop (𝓝 0) := by
    simpa using (Real.tendsto_log_atTop.inv_tendsto_atTop).const_mul (d * B)
  refine squeeze_zero_norm' (a := fun x => d * B * (Real.log x)⁻¹) ?_ hlim
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, ← div_eq_mul_inv]
  exact abs_logAvg_dilate_sub_le hB hd hx

/-- **Residues are uniform.** `L(1_{n ≡ r mod Q}) = 1/Q`. -/
theorem limAvg_residue (hU : (U : Filter ℝ) ≤ atTop) {Q : ℕ} [NeZero Q] (r : ZMod Q) :
    limAvg U (fun n => if (n : ZMod Q) = r then 1 else 0) = 1 / Q := by
  set g : ZMod Q → ℕ → ℝ := fun r n => if (n : ZMod Q) = r then 1 else 0 with hg
  have hstep : ∀ r, limAvg U (g (r + 1)) = limAvg U (g r) := by
    intro r
    have h := limAvg_shift hU (bdd_indicator (fun n => (n : ZMod Q) = r + 1))
    rw [← h]
    congr 1
    funext n
    simp only [hg, Nat.cast_add, Nat.cast_one, add_left_inj]
  have hall : ∀ k : ℕ, limAvg U (g k) = limAvg U (g 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, hstep, ih]
  have hconst : ∀ r, limAvg U (g r) = limAvg U (g 0) := by
    intro r
    have := hall r.val
    rwa [ZMod.natCast_zmod_val] at this
  have hsum : ∑ r : ZMod Q, limAvg U (g r) = 1 := by
    rw [← limAvg_sum hU _ fun r _ => bdd_indicator _]
    have : (fun n => ∑ r : ZMod Q, g r n) = fun _ => 1 := by
      funext n
      simp [hg]
    rw [this, limAvg_const hU]
  simp only [hconst, sum_const, card_univ, ZMod.card, nsmul_eq_mul] at hsum
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have := hconst r
  simp only [hg] at this ⊢
  rw [this]
  field_simp
  linarith

/-- A bounded sequence whose limit functionals all vanish has vanishing logarithmic averages. -/
theorem tendsto_logAvg_of_forall_limAvg_eq_zero {f : ℕ → ℝ} (hf : Bdd f)
    (h : ∀ U : Ultrafilter ℝ, (U : Filter ℝ) ≤ atTop → limAvg U f = 0) :
    Tendsto (logAvg f) atTop (𝓝 0) := by
  rw [tendsto_iff_ultrafilter]
  intro U hU
  have := tendsto_limAvg hU hf
  rwa [h U hU] at this

/-! ## Laws of finite-valued sequences -/

/-- The law `a ↦ L(1_{g = a})` of a finite-valued sequence. -/
def law (U : Ultrafilter ℝ) {α : Type*} [DecidableEq α] (g : ℕ → α) (a : α) : ℝ :=
  limAvg U (fun n => if g n = a then 1 else 0)

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem law_nonneg (hU : (U : Filter ℝ) ≤ atTop) (g : ℕ → α) (a : α) : 0 ≤ law U g a :=
  limAvg_nonneg hU (bdd_indicator _) fun n => by split_ifs <;> norm_num

/-- `L(F ∘ g) = Σ_a F(a) P(g = a)`. -/
theorem limAvg_comp (hU : (U : Filter ℝ) ≤ atTop) [Fintype α] (g : ℕ → α) (F : α → ℝ) :
    limAvg U (fun n => F (g n)) = ∑ a, F a * law U g a := by
  have hpt : (fun n => F (g n)) = fun n => ∑ a, F a * (if g n = a then 1 else 0) := by
    funext n
    simp
  rw [hpt, limAvg_sum hU _ fun a _ => (bdd_indicator _).const_mul (F a)]
  refine sum_congr rfl fun a _ => ?_
  rw [limAvg_const_mul hU (bdd_indicator _)]
  rfl

theorem sum_law (hU : (U : Filter ℝ) ≤ atTop) [Fintype α] (g : ℕ → α) : ∑ a, law U g a = 1 := by
  have h := limAvg_comp hU g fun _ => 1
  simp only [one_mul] at h
  rw [← h, limAvg_const hU]

/-- The law of `F ∘ g` is the pushforward of the law of `g`. -/
theorem law_comp (hU : (U : Filter ℝ) ≤ atTop) [Fintype α] (g : ℕ → α) (F : α → β) (b : β) :
    law U (fun n => F (g n)) b = ∑ a ∈ univ.filter (fun a => F a = b), law U g a := by
  have h := limAvg_comp hU g fun a => if F a = b then 1 else 0
  simp only [ite_mul, one_mul, zero_mul] at h
  rw [law, h, sum_filter]

/-- The law is shift invariant. -/
theorem law_shift_add (hU : (U : Filter ℝ) ≤ atTop) (g : ℕ → α) (m : ℕ) :
    law U (fun n => g (n + m)) = law U g := by
  funext a
  exact limAvg_shift_add hU (bdd_indicator (fun n => g n = a)) m

end

end GaloisForLFunctions.LogarithmicChowla
