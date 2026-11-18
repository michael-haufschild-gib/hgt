import GaloisForLFunctions.HTGeometry.ReflectionlessWell

/-!
# Darboux chains for the reflectionless well

Joint value and derivative transport preserves the spectral gap products
at both ends. The Riccati cross-ratio determines the entire translated
one-soliton family after any finite ordered sequence of pivots.
-/

namespace GaloisForLFunctions.HTGeometry.Darboux
open Filter Set Topology DispersivePDE
noncomputable section

/-- Simultaneous Darboux transformation of a mode and its derivative.
The original potential cancels from the second component. -/
def transport (μ energy p : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2-p*z.1,(energy-μ)*z.1-p*(z.2-p*z.1))

/-- The first-order system intertwines the two potentials at a Riccati pivot. -/
theorem transport_equation {u v p : ℝ → ℝ} {μ energy V x : ℝ}
    (hu : HasDerivAt u (v x) x) (hv : HasDerivAt v ((V+energy)*u x) x)
    (hp : HasDerivAt p (V+μ-p x^2) x) :
    let J := fun t => transport μ energy (p t) (u t,v t)
    HasDerivAt (fun t => (J t).1) (J x).2 x ∧
      HasDerivAt (fun t => (J t).2) ((V - 2*(V+μ-p x^2)+energy)*(J x).1) x := by
  have h₁ : HasDerivAt (fun t => v t-p t*u t) (transport μ energy (p x) (u x,v x)).2 x := by
    apply (hv.sub (hp.mul hu)).congr_deriv
    dsimp [transport]
    ring
  refine ⟨h₁,?_⟩
  apply ((hu.const_mul (energy-μ)).sub (hp.mul h₁)).congr_deriv
  dsimp [transport]
  ring

/-- The Wronskian of two solutions at the same spectral value is multiplied
by the spectral gap. At the pivot value the map has rank one. -/
theorem transport_wronskian (μ energy p : ℝ) (z w : ℝ × ℝ) :
    (transport μ energy p z).1*(transport μ energy p w).2 -
      (transport μ energy p z).2*(transport μ energy p w).1 = (μ-energy)*(z.1*w.2-z.2*w.1) := by
  dsimp [transport]
  ring

private theorem transport_eigenline (a b c : ℝ) :
    transport (a^2) (b^2) a (c,b*c) = ((b-a)*c,b*((b-a)*c)) := by
  apply Prod.ext <;> dsimp [transport] <;> ring

/-- Successive transport of the pairs after dividing out their respective
leading exponential factors. Division is only needed for a pivot slope. -/
def chain : List ℝ → (ℝ → ℝ → ℝ × ℝ) → ℝ → ℝ → ℝ × ℝ
  | [], J => J
  | a :: rest, J => chain rest fun b x =>
      transport (a^2) (b^2) ((J a x).2/(J a x).1) (J b x)

private theorem transport_limit {a b c d : ℝ} {J K : ℝ → ℝ × ℝ}
    (hc : c ≠ 0) (hJ : Tendsto J atBot (𝓝 (c,a*c))) (hK : Tendsto K atBot (𝓝 (d,b*d))) :
    Tendsto (fun x => transport (a^2) (b^2) ((J x).2/(J x).1) (K x)) atBot
      (𝓝 ((b-a)*d,b*((b-a)*d))) := by
  have hp : Tendsto (fun x => (J x).2/(J x).1) atBot (𝓝 a) := by
    have h₁ : Tendsto (fun x => (J x).1) atBot (𝓝 c) := (continuous_fst.tendsto _).comp hJ
    have h₂ : Tendsto (fun x => (J x).2) atBot (𝓝 (a*c)) := (continuous_snd.tendsto _).comp hJ
    have h := h₂.div h₁ hc
    change Tendsto (fun x => (J x).2/(J x).1) atBot (𝓝 ((a*c)/c)) at h
    rwa [mul_div_cancel_right₀ _ hc] at h
  rw [← transport_eigenline]
  have hcont : Continuous (fun z : ℝ × (ℝ × ℝ) => transport (a^2) (b^2) z.1 z.2) := by
    unfold transport
    fun_prop
  exact (hcont.tendsto _).comp (hp.prodMk_nhds hK)

/-- A single initial value-and-slope asymptotic propagates through every
finite ordered chain with spectral law `α² + const`. The new coefficients
are explicit even when the first exponent is zero. -/
theorem chain_endpoint (pivots : List ℝ) (b : ℝ) (J : ℝ → ℝ → ℝ × ℝ) (c : ℝ → ℝ)
    (horder : (pivots ++ [b]).Pairwise (· < ·))
    (h : ∀ a ∈ pivots ++ [b], 0 < c a ∧ Tendsto (J a) atBot (𝓝 (c a,a*c a))) :
    let d := c b * (pivots.map (fun a => b-a)).prod
    0 < d ∧ Tendsto (chain pivots J b) atBot (𝓝 (d,b*d)) := by
  induction pivots generalizing J c with
  | nil => simpa [chain] using h b (by simp)
  | cons a as ih =>
    obtain ⟨ha,htail⟩ := List.pairwise_cons.mp horder
    obtain ⟨hc,hlim⟩ := h a (by simp)
    let J' := fun w x => transport (a^2) (w^2) ((J a x).2/(J a x).1) (J w x)
    let c' := fun w => (w-a)*c w
    have hh (w : ℝ) (hw : w ∈ as ++ [b]) : 0 < c' w ∧ Tendsto (J' w) atBot (𝓝 (c' w,w*c' w)) := by
      obtain ⟨hpos,hl⟩ := h w (List.mem_cons_of_mem _ hw)
      exact ⟨mul_pos (sub_pos.mpr (ha w hw)) hpos,transport_limit hc.ne' hlim hl⟩
    have H := ih J' c' htail hh
    simpa only [chain,J',c',List.map_cons,List.prod_cons,mul_assoc,mul_left_comm,mul_comm] using H

/-- Riccati coordinate of the original reflectionless well. -/
def wellSlope (l x : ℝ) := Real.exp l * solitonT (Real.exp l*x)

private theorem wellSlope_deriv (l x : ℝ) :
    HasDerivAt (wellSlope l) (0+(Real.exp l)^2-(wellSlope l x)^2) x := by
  have h := ((hasDerivAt_solitonT (Real.exp l*x)).comp x ((hasDerivAt_id x).const_mul (Real.exp l))).const_mul (Real.exp l)
  apply h.congr_deriv
  dsimp [solitonQ,wellSlope]
  ring

/-- Darboux transforms the free exponential into an eigenmode of the
reflectionless well for every real energy parameter. -/
def wellMode (l b x : ℝ) : ℝ × ℝ :=
  transport ((Real.exp l)^2) (b^2) (wellSlope l x) (Real.exp (b*x),b*Real.exp (b*x))

theorem wellMode_equation (l b x : ℝ) :
    HasDerivAt (fun t => (wellMode l b t).1) (wellMode l b x).2 x ∧
    HasDerivAt (fun t => (wellMode l b t).2)
      ((reflectionlessWellPotential l x+b^2)*(wellMode l b x).1) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (b*t)) (b*Real.exp (b*x)) x := by
    apply (((hasDerivAt_id x).const_mul b).exp).congr_deriv
    simp only [id_eq,mul_one]
    ring
  have he' : HasDerivAt (fun t : ℝ => b*Real.exp (b*t)) ((0+b^2)*Real.exp (b*x)) x := by
    apply (he.const_mul b).congr_deriv
    ring
  have hh := transport_equation (u := fun t => Real.exp (b*t)) (v := fun t => b*Real.exp (b*t))
    (p := wellSlope l) (V := 0) (energy := b^2) (μ := (Real.exp l)^2) he he' (wellSlope_deriv l x)
  have hq : 0-2*(0+(Real.exp l)^2-(wellSlope l x)^2) = reflectionlessWellPotential l x := by
    dsimp [wellSlope,reflectionlessWellPotential,solitonQ]
    ring
  rw [hq] at hh
  exact hh

/-- The Riccati coordinate of the translated one-soliton well after a pivot. -/
def shiftPivot (a k p : ℝ) := (k*p-a^2)/(k-p)

private theorem shiftPivot_mem {a k p : ℝ} (hk : a < k) (hp : p ∈ Ioo (-a) a) :
    shiftPivot a k p ∈ Ioo (-a) a := by
  have hd := sub_pos.mpr (hp.2.trans hk)
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith only [mul_pos (sub_pos.mpr hk) (show 0 < p+a by linarith [hp.1])]
  · apply (div_lt_iff₀ hd).mpr
    nlinarith only [mul_pos (sub_pos.mpr hp.2) (show 0 < k+a by linarith [hp.1,hp.2,hk])]

private theorem shiftPivot_deriv {a k : ℝ} {p : ℝ → ℝ} {x : ℝ} (hk : a < k)
    (hp : p x ∈ Ioo (-a) a) (hd : HasDerivAt p (a^2-p x^2) x) :
    HasDerivAt (fun t => shiftPivot a k (p t)) (a^2-(shiftPivot a k (p x))^2) x := by
  have hn := (sub_pos.mpr (hp.2.trans hk)).ne'
  apply (((hd.const_mul k).sub_const (a^2)).fun_div (hd.const_sub k) hn).congr_deriv
  unfold shiftPivot
  field_simp [hn]
  ring

/-- The positive cross-ratio is multiplied by a constant. Thus Darboux steps
translate the center of a one-soliton well, and commute in this coordinate. -/
theorem shiftPivot_ratio (l : ℝ) (k : Ioi (Real.exp l))
    (p : Ioo (-Real.exp l) (Real.exp l)) :
    (Real.exp l + shiftPivot (Real.exp l) k p)/(Real.exp l-shiftPivot (Real.exp l) k p) =
    (Real.exp l+p)/(Real.exp l-p)*((k.val-Real.exp l)/(k.val+Real.exp l)) := by
  let a := Real.exp l
  change (a+shiftPivot a k p)/(a-shiftPivot a k p) = (a+p)/(a-p)*((k.val-a)/(k.val+a))
  have hd := (sub_pos.mpr (p.property.2.trans k.property)).ne'
  have hp : a-p.val ≠ 0 := (sub_pos.mpr p.property.2).ne'
  have hk : k.val+a ≠ 0 := (add_pos ((Real.exp_pos l).trans k.property) (Real.exp_pos l)).ne'
  have hp' : a+shiftPivot a k p = (a+p.val)*(k.val-a)/(k.val-p.val) := by
    unfold shiftPivot
    field_simp [hd]
    ring
  have hm' : a-shiftPivot a k p = (a-p.val)*(k.val+a)/(k.val-p.val) := by
    unfold shiftPivot
    field_simp [hd]
    ring
  rw [hp',hm']
  field_simp [hd,hp,hk]

/-- Actual iterated transforms with logarithmic derivatives of the current
pivot solutions. -/
def applyPivots {α : Type*} : List α → (α → ℝ → ℝ) → α → ℝ → ℝ
  | [], F => F
  | k :: ks, F => applyPivots ks fun b x =>
      deriv (F b) x - deriv (F k) x/F k x * F b x

private def dressed (p : ℝ → ℝ) (c b x : ℝ) := c*Real.exp (b*x)*(b-p x)

private theorem dressed_deriv {a b c x : ℝ} {p : ℝ → ℝ}
    (hd : HasDerivAt p (a^2-p x^2) x) :
    HasDerivAt (dressed p c b) (c*Real.exp (b*x)*(b*(b-p x)-(a^2-p x^2))) x := by
  apply (((((hasDerivAt_id x).const_mul b).exp).const_mul c).mul (hd.const_sub b)).congr_deriv
  dsimp
  ring

private theorem darbouxdressed {a k b c d x : ℝ} {p : ℝ → ℝ}
    (hk : a < k) (hp : p x ∈ Ioo (-a) a) (hd : HasDerivAt p (a^2-p x^2) x) (hc : c ≠ 0) :
    deriv (dressed p d b) x - deriv (dressed p c k) x / dressed p c k x * dressed p d b x =
      dressed (fun y => shiftPivot a k (p y)) ((b-k)*d) b x := by
  rw [(dressed_deriv hd).deriv,(dressed_deriv hd).deriv]
  unfold dressed shiftPivot
  field_simp [hc,Real.exp_ne_zero,(sub_pos.mpr (hp.2.trans hk)).ne']
  ring

/-- Riccati coordinate after all the pivots in succession. -/
def shiftedSlope {a : ℝ} : List (Ioi a) → (ℝ → ℝ) → ℝ → ℝ
  | [], p => p
  | k :: ks, p => shiftedSlope ks (fun y => shiftPivot a k (p y))

private theorem pivots_formula {a : ℝ} (ks : List (Ioi a)) (b : Ioi a)
    (hord : (ks++[b]).Pairwise (· < ·)) (p : ℝ → ℝ) (c : Ioi a → ℝ)
    (hp : ∀ x, p x ∈ Ioo (-a) a) (hd : ∀ x, HasDerivAt p (a^2-p x^2) x)
    (hc : ∀ k ∈ ks++[b], 0 < c k) :
    applyPivots ks (fun z => dressed p (c z) z) b =
      dressed (shiftedSlope ks p) (c b*(ks.map fun k => b.val-k.val).prod) b := by
  induction ks generalizing p c with
  | nil => simp [applyPivots,shiftedSlope]
  | cons k ks ih =>
    obtain ⟨hk,hs⟩ := List.pairwise_cons.mp hord
    let q := fun y => shiftPivot a k (p y)
    let e := fun z : Ioi a => (z.val-k.val)*c z
    have hstep : (fun (z : Ioi a) x =>
        deriv (dressed p (c z) z) x - deriv (dressed p (c k) k) x/dressed p (c k) k x *
          dressed p (c z) z x) = (fun z => dressed q (e z) z) := by
      funext z x
      exact darbouxdressed k.property (hp x) (hd x) (hc k (by simp)).ne'
    rw [applyPivots,hstep,ih hs q e (fun x => shiftPivot_mem k.property (hp x))
      (fun x => shiftPivot_deriv k.property (hp x) (hd x))
      (fun z hz => mul_pos (sub_pos.mpr (hk z hz)) (hc z (List.mem_cons_of_mem _ hz)))]
    simp only [shiftedSlope,List.map_cons,List.prod_cons,e,q,mul_comm,mul_assoc]

private theorem wellSlope_mem (l x : ℝ) : wellSlope l x ∈ Ioo (-Real.exp l) (Real.exp l) := by
  let a := Real.exp l
  change -(a) < a * Real.tanh (a*x) ∧ a * Real.tanh (a*x) < a
  have h := Real.tanh_lt_one (-(a*x))
  rw [Real.tanh_neg] at h
  constructor
  · simpa using mul_lt_mul_of_pos_left (show -1 < Real.tanh (a*x) by linarith only [h]) (Real.exp_pos l)
  · simpa using mul_lt_mul_of_pos_left (Real.tanh_lt_one _) (Real.exp_pos l)

private theorem shiftedSlope_mem {a : ℝ} (ks : List (Ioi a)) {p : ℝ → ℝ}
    (hp : ∀ x, p x ∈ Ioo (-a) a) (x : ℝ) : shiftedSlope ks p x ∈ Ioo (-a) a := by
  induction ks generalizing p with
  | nil => exact hp x
  | cons k ks ih => exact ih (fun y => shiftPivot_mem k.property (hp y))

/-- Exact global Darboux chain in the reflectionless well, at every position.
The factor multiplying the shifted eigenmode is the product of spectral gaps. -/
theorem wellMode_pivots (l : ℝ) (b : Ioi (Real.exp l))
    (ks : {s : List (Ioi (Real.exp l)) // (s++[b]).Pairwise (· < ·)}) (x : ℝ) :
    applyPivots ks.val (fun k t => (wellMode l k t).1) b x =
      (ks.val.map fun k => b.val-k.val).prod * Real.exp (b.val*x) *
        (b.val-shiftedSlope ks.val (wellSlope l) x) := by
  have he : (fun (k : Ioi (Real.exp l)) t => (wellMode l k t).1) =
      (fun k : Ioi (Real.exp l) => dressed (wellSlope l) 1 k.val) := by
    funext k t
    dsimp [wellMode,transport,dressed]
    ring
  rw [he,pivots_formula ks.val b ks.property _ (fun _ => 1) (wellSlope_mem l)
    (fun t => by simpa only [zero_add] using wellSlope_deriv l t) (by simp)]
  simp only [dressed,one_mul]

/-- Every pivot is globally nodeless, at every finite ordered stage. -/
theorem wellMode_pivots_pos (l : ℝ) (b : Ioi (Real.exp l))
    (ks : {s : List (Ioi (Real.exp l)) // (s++[b]).Pairwise (· < ·)}) (x : ℝ) :
    0 < applyPivots ks.val (fun k t => (wellMode l k t).1) b x := by
  rw [wellMode_pivots]
  have hg : ∀ k ∈ ks.val, k < b := fun k hk =>
    (List.pairwise_append.mp ks.property).2.2 k hk b (by simp)
  have hprod : 0 < (ks.val.map fun k => b.val-k.val).prod :=
    List.prod_pos (fun t ht => by obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht; exact sub_pos.mpr (hg k hk))
  exact mul_pos (mul_pos hprod (Real.exp_pos _)) (sub_pos.mpr
    ((shiftedSlope_mem ks.val (wellSlope_mem l) x).2.trans b.property))

theorem shiftedSlope_ratio (l : ℝ) (ks : List (Ioi (Real.exp l))) (x : ℝ) :
    let a := Real.exp l
    let p := shiftedSlope ks (wellSlope l) x
    (a+p)/(a-p) = (a+wellSlope l x)/(a-wellSlope l x)*
      (ks.map fun k => (k.val-a)/(k.val+a)).prod := by
  let a := Real.exp l
  have he (rs : List (Ioi a)) (p : ℝ → ℝ) (hp : ∀ t, p t ∈ Ioo (-a) a) :
      (a+shiftedSlope rs p x)/(a-shiftedSlope rs p x) =
        (a+p x)/(a-p x)*(rs.map fun k => (k.val-a)/(k.val+a)).prod := by
    induction rs generalizing p with
    | nil => simp [shiftedSlope]
    | cons k rs ih =>
      have h := ih (fun y => shiftPivot a k (p y)) (fun y => shiftPivot_mem k.property (hp y))
      rw [shiftedSlope]
      rw [h,shiftPivot_ratio l k ⟨p x,hp x⟩,List.map_cons,List.prod_cons,mul_assoc]
  exact he ks (wellSlope l) (wellSlope_mem l)

/-- The end values of the Riccati coordinate survive every finite dressing.
Both limiting backgrounds are therefore the same as for the initial well. -/
theorem shiftedSlope_limits (l : ℝ) (ks : List (Ioi (Real.exp l))) :
    Tendsto (shiftedSlope ks (wellSlope l)) atBot (𝓝 (-Real.exp l)) ∧
    Tendsto (shiftedSlope ks (wellSlope l)) atTop (𝓝 (Real.exp l)) := by
  let a := Real.exp l
  have propagate (rs : List (Ioi a)) (p : ℝ → ℝ) (e : ℝ) (f : Filter ℝ)
      (he : e^2 = a^2) (he' : e ≤ a) (h : Tendsto p f (𝓝 e)) :
      Tendsto (shiftedSlope rs p) f (𝓝 e) := by
    induction rs generalizing p with
    | nil => exact h
    | cons k rs ih =>
      apply ih
      have hn := (sub_pos.mpr (he'.trans_lt k.property)).ne'
      have hlim := ((h.const_mul k.val).sub_const (a^2)).div (h.const_sub k.val) hn
      have hfix : (k.val*e-a^2)/(k.val-e) = e := (div_eq_iff hn).mpr (by rw [← he]; ring)
      rwa [hfix] at hlim
  have ht : Tendsto (fun x : ℝ => Real.tanh (a*x)) atTop (𝓝 1) := by
    simpa only [Function.comp_def,id_eq] using
      tendsto_tanh_atTop_one.comp (tendsto_id.const_mul_atTop (Real.exp_pos l))
  have hb : Tendsto (fun x : ℝ => Real.tanh (a*x)) atBot (𝓝 (-1)) := by
    simpa only [Function.comp_def,mul_neg,Real.tanh_neg,neg_neg] using ht.neg.comp tendsto_neg_atBot_atTop
  have hb' := hb.const_mul a
  change Tendsto (wellSlope l) atBot (𝓝 (a * (-1))) at hb'
  have ht' := ht.const_mul a
  change Tendsto (wellSlope l) atTop (𝓝 (a * 1)) at ht'
  rw [mul_neg_one] at hb'
  rw [mul_one] at ht'
  exact ⟨propagate ks (wellSlope l) (-a) atBot (by ring) (by linarith only [Real.exp_pos l]) hb',
    propagate ks (wellSlope l) a atTop rfl le_rfl ht'⟩

private theorem shiftedSlope_deriv {a : ℝ} (ks : List (Ioi a)) (p : ℝ → ℝ)
    (hp : ∀ x, p x ∈ Ioo (-a) a) (hd : ∀ x, HasDerivAt p (a^2-p x^2) x) (x : ℝ) :
    HasDerivAt (shiftedSlope ks p) (a^2-(shiftedSlope ks p x)^2) x := by
  induction ks generalizing p with
  | nil => exact hd x
  | cons k ks ih =>
    exact ih _ (fun y => shiftPivot_mem k.property (hp y))
      (fun y => shiftPivot_deriv k.property (hp y) (hd y))

/-- Value and first derivative have positive exponential asymptotics on both
ends. The exact gap product applies to arbitrary finite ordered Darboux chains. -/
theorem wellMode_pivots_asymptotics (l : ℝ) (b : Ioi (Real.exp l))
    (ks : {s : List (Ioi (Real.exp l)) // (s++[b]).Pairwise (· < ·)}) :
    let a := Real.exp l
    let c := (ks.val.map fun k => b.val-k.val).prod
    let F := applyPivots ks.val (fun k t => (wellMode l k t).1) b
    let J := fun x => (F x / Real.exp (b.val*x), deriv F x / Real.exp (b.val*x))
    Tendsto J atBot (𝓝 (c*(b.val+a),b.val*(c*(b.val+a)))) ∧
    Tendsto J atTop (𝓝 (c*(b.val-a),b.val*(c*(b.val-a)))) := by
  dsimp only
  let a := Real.exp l
  let c := (ks.val.map fun k => b.val-k.val).prod
  let p := shiftedSlope ks.val (wellSlope l)
  have he : applyPivots ks.val (fun k t => (wellMode l k t).1) b = dressed p c b :=
    funext (wellMode_pivots l b ks)
  rw [he]
  have hd (x : ℝ) : HasDerivAt p (a^2-p x^2) x := shiftedSlope_deriv _ _ (wellSlope_mem l)
    (fun y => by simpa only [zero_add] using wellSlope_deriv l y) x
  have hf : (fun x => (dressed p c b x/Real.exp (b.val*x), deriv (dressed p c b) x/Real.exp (b.val*x))) =
      (fun x => (c*(b.val-p x),c*(b.val*(b.val-p x)-(a^2-p x^2)))) := by
    funext x
    rw [(dressed_deriv (hd x)).deriv]
    unfold dressed
    apply Prod.ext <;> dsimp <;> field_simp [Real.exp_ne_zero]
  rw [hf]
  have H (e : ℝ) (f : Filter ℝ) (h : Tendsto p f (𝓝 e)) (hfix : e^2 = a^2) :
      Tendsto (fun x => (c*(b.val-p x),c*(b.val*(b.val-p x)-(a^2-p x^2)))) f
        (𝓝 (c*(b.val-e),b.val*(c*(b.val-e)))) := by
    have hh := ((h.const_sub b.val).const_mul c).prodMk_nhds
      ((((h.const_sub b.val).const_mul b.val).sub ((h.pow 2).const_sub (a^2))).const_mul c)
    simpa only [hfix,sub_self,sub_zero,mul_left_comm c b.val] using hh
  obtain ⟨hb,ht⟩ := shiftedSlope_limits l ks.val
  exact ⟨by simpa only [sub_neg_eq_add] using H (-a) atBot hb (by ring),H a atTop ht rfl⟩

#print axioms transport_equation
#print axioms transport_wronskian
#print axioms chain_endpoint
#print axioms shiftPivot_ratio
#print axioms wellMode_equation
#print axioms shiftedSlope_limits
#print axioms wellMode_pivots_asymptotics
#print axioms wellMode_pivots
#print axioms wellMode_pivots_pos
end
end GaloisForLFunctions.HTGeometry.Darboux
