import GaloisForLFunctions.HTGeometry.KleinbockMargulis.SmoothGoodOne

/-!
# Lemma 3.3: the sublevel estimate on a cube in `d` variables

A function `f` on an open set `V ⊆ ℝ^d` satisfies the hypotheses `(3.4≤)`, `(3.4≥)` of
Kleinbock–Margulis when along every coordinate line it has a `k`-fold derivative chain whose top
member is sandwiched between `A₂ > 0` and `A₁`; this is `SandwichedChains`.  For a `C^k` function
the chain is the sequence of pure partial derivatives `∂_i^j f`, so no mixed derivative is needed.

The estimate `(3.5)` is proved by induction on `d`.  The one-dimensional case is
`exists_good_const_one_dim`.  For the induction step the cube is split as `B₁ × B'`; Fubini in
the first coordinate gives the measure of a sublevel set as an integral of the measures of its
slices, and the level `λ` at which a slice is declared "large" is optimised at the end.

Unlike the paper, the argument here never forms the sup of `|f|` over a face: the inductive
statement is the pointwise one, so a *fixed* point `z` of the cube is carried through both the
inductive hypothesis (applied on the face through `z`) and the one-dimensional estimate (applied
on the line through `z`).  Lemma 3.1(c) is therefore not needed.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d : ℕ}

/-! ### Coordinate-line derivative chains -/

/-- `f` is continuous on `V` and has, along every coordinate line, a `k`-fold derivative chain
whose top member has absolute value between `A₂` and `A₁` at every point of `V`.  This is the
Lean form of the hypotheses `(3.4≤)`, `(3.4≥)` of Lemma 3.3. -/
structure SandwichedChains (k : ℕ) (V : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) (A₁ A₂ : ℝ) :
    Prop where
  cont : ContinuousOn f V
  chain : ∀ (i : Fin d) (x : Fin d → ℝ), ∃ F : ℕ → ℝ → ℝ,
    (∀ t, F 0 t = f (Function.update x i t)) ∧
    IsDerivChain F {t | Function.update x i t ∈ V} ∧
    (∀ t, Function.update x i t ∈ V → |F k t| ≤ A₁ ∧ A₂ ≤ |F k t|)

theorem SandwichedChains.mono {k : ℕ} {V W : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} {A₁ A₂ : ℝ}
    (H : SandwichedChains k V f A₁ A₂) (h : W ⊆ V) : SandwichedChains k W f A₁ A₂ where
  cont := H.cont.mono h
  chain := by
    intro i x
    obtain ⟨F, hF0, hFc, hFb⟩ := H.chain i x
    exact ⟨F, hF0, fun j t ht => hFc j t (h ht), fun t ht => hFb t (h ht)⟩

/-! ### Fubini in the first coordinate -/

theorem measurable_cons :
    Measurable (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : Fin (d + 1) → ℝ)) := by
  refine measurable_pi_lambda _ fun j => ?_
  induction j using Fin.cases with
  | zero => simp only [Fin.cons_zero]; fun_prop
  | succ i => simp only [Fin.cons_succ]; fun_prop

/-- Fubini in the first coordinate: the measure of a set in `ℝ^{d+1}` is the integral of the
measures of its slices. -/
theorem volume_eq_lintegral_slice {s : Set (Fin (d + 1) → ℝ)} (hs : MeasurableSet s) :
    volume s = ∫⁻ t : ℝ, volume {x' : Fin d → ℝ | Fin.cons t x' ∈ s} := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  set T : Set (ℝ × (Fin d → ℝ)) := {p | (Fin.cons p.1 p.2 : Fin (d + 1) → ℝ) ∈ s} with hTdef
  have hT : MeasurableSet T := measurable_cons hs
  have hpre : e ⁻¹' T = s := by
    ext x
    show Fin.cons ((e x).1) ((e x).2) ∈ s ↔ x ∈ s
    rw [show ((e x).1 : ℝ) = x 0 from rfl, show ((e x).2 : Fin d → ℝ) = Fin.tail x from rfl,
      Fin.cons_self_tail]
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => (volume : Measure ℝ)) 0).measure_preimage hT.nullMeasurableSet
  rw [← hpre]
  rw [show (volume : Measure (Fin (d + 1) → ℝ)) = Measure.pi fun _ => volume from volume_pi]
  rw [hmp, Measure.prod_apply hT]
  rfl

/-! ### Cubes split as a product -/

theorem cons_mem_ball {x₀ : Fin (d + 1) → ℝ} {r t : ℝ} (hr : 0 < r) {x' : Fin d → ℝ} :
    Fin.cons t x' ∈ ball x₀ r ↔ t ∈ ball (x₀ 0) r ∧ x' ∈ ball (Fin.tail x₀) r := by
  rw [ball_pi _ hr, ball_pi (Fin.tail x₀) hr]
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun j => by simpa [Fin.tail] using h j.succ⟩
  · rintro ⟨h0, h'⟩ j
    induction j using Fin.cases with
    | zero => simpa using h0
    | succ i => simpa [Fin.tail] using h' i

theorem volume_ball_pow {x₀ : Fin d → ℝ} {r : ℝ} (hr : 0 < r) :
    volume (ball x₀ r) = ENNReal.ofReal ((2 * r) ^ d) := by
  rw [Real.volume_pi_ball _ hr]
  simp


/-! ### Restricting the chains to a face and to a line -/

theorem continuous_cons_left (t : ℝ) :
    Continuous fun x' : Fin d → ℝ => (Fin.cons t x' : Fin (d + 1) → ℝ) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.cases with
  | zero => simp only [Fin.cons_zero]; fun_prop
  | succ i => simp only [Fin.cons_succ]; fun_prop

theorem continuous_cons_right (x' : Fin d → ℝ) :
    Continuous fun t : ℝ => (Fin.cons t x' : Fin (d + 1) → ℝ) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.cases with
  | zero => simp only [Fin.cons_zero]; fun_prop
  | succ i => simp only [Fin.cons_succ]; fun_prop

theorem update_cons_succ (t : ℝ) (x' : Fin d → ℝ) (i : Fin d) (u : ℝ) :
    Function.update (Fin.cons t x' : Fin (d + 1) → ℝ) i.succ u
      = Fin.cons t (Function.update x' i u) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [(Fin.succ_ne_zero i).symm]
  | succ m => simp [Function.update_apply, Fin.succ_inj]

theorem update_cons_zero (t : ℝ) (x' : Fin d → ℝ) (u : ℝ) :
    Function.update (Fin.cons t x' : Fin (d + 1) → ℝ) 0 u = Fin.cons u x' := by
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ m => simp [Fin.succ_ne_zero]

/-- The restriction of `f` to the face `x₁ = t` again has sandwiched coordinate chains. -/
theorem SandwichedChains.slice {k : ℕ} {V : Set (Fin (d + 1) → ℝ)}
    {f : (Fin (d + 1) → ℝ) → ℝ} {A₁ A₂ : ℝ} (H : SandwichedChains k V f A₁ A₂) (t : ℝ) :
    SandwichedChains k {x' : Fin d → ℝ | (Fin.cons t x' : Fin (d + 1) → ℝ) ∈ V}
      (fun x' => f (Fin.cons t x')) A₁ A₂ where
  cont := H.cont.comp (continuous_cons_left t).continuousOn fun _ hx' => hx'
  chain := by
    intro i x'
    obtain ⟨F, hF0, hFc, hFb⟩ := H.chain i.succ (Fin.cons t x')
    refine ⟨F, fun u => ?_, fun j u hu => ?_, fun u hu => ?_⟩
    · rw [hF0 u, update_cons_succ]
    · simp only [Set.mem_setOf_eq] at hu
      rw [← update_cons_succ t x' i u] at hu
      exact hFc j u hu
    · simp only [Set.mem_setOf_eq] at hu
      rw [← update_cons_succ t x' i u] at hu
      exact hFb u hu

/-- The restriction of `f` to the line through `x'` in the first coordinate direction has a
sandwiched `k`-fold derivative chain. -/
theorem SandwichedChains.line {k : ℕ} {V : Set (Fin (d + 1) → ℝ)}
    {f : (Fin (d + 1) → ℝ) → ℝ} {A₁ A₂ : ℝ} (H : SandwichedChains k V f A₁ A₂)
    (x' : Fin d → ℝ) :
    ∃ F : ℕ → ℝ → ℝ, (∀ t, F 0 t = f (Fin.cons t x')) ∧
      IsDerivChain F {t | (Fin.cons t x' : Fin (d + 1) → ℝ) ∈ V} ∧
      ∀ t, (Fin.cons t x' : Fin (d + 1) → ℝ) ∈ V → |F k t| ≤ A₁ ∧ A₂ ≤ |F k t| := by
  obtain ⟨F, hF0, hFc, hFb⟩ := H.chain 0 (Fin.cons 0 x')
  refine ⟨F, fun u => ?_, fun j u hu => ?_, fun u hu => ?_⟩
  · rw [hF0 u, update_cons_zero]
  · simp only [Set.mem_setOf_eq] at hu
    rw [← update_cons_zero (0 : ℝ) x' u] at hu
    exact hFc j u hu
  · rw [← update_cons_zero (0 : ℝ) x' u] at hu
    exact hFb u hu

/-! ### Measurability of the sublevel set -/

theorem isOpen_sublevel {V : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f V)
    {x₀ : Fin d → ℝ} {r ε : ℝ} (hsub : ball x₀ r ⊆ V) :
    IsOpen {x ∈ ball x₀ r | |f x| < ε} := by
  have hEq : {x ∈ ball x₀ r | |f x| < ε} = ball x₀ r ∩ (fun x => |f x|) ⁻¹' (Iio ε) := rfl
  rw [hEq]
  exact ((hf.mono hsub).abs).isOpen_inter_preimage isOpen_ball isOpen_Iio


/-! ### The inductive statement -/

/-- The `d`-dimensional sublevel estimate `(3.5)` with constant `K`, in pointwise form: the
measure of `{|f| < ε}` inside a cube of side `2r` times `|f z|^{1/dk}` is at most
`K ε^{1/dk} (2r)^d`, for every point `z` of the cube. -/
def CubeEstimate (d k : ℕ) (A₁ A₂ K : ℝ) : Prop :=
  ∀ (V : Set (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ), SandwichedChains k V f A₁ A₂ →
    ∀ (x₀ : Fin d → ℝ) (r : ℝ), 0 < r → ball x₀ r ⊆ V → ∀ ε : ℝ, 0 < ε → ∀ z ∈ ball x₀ r,
      (volume {x ∈ ball x₀ r | |f x| < ε}).toReal * |f z| ^ (((d : ℝ) * k)⁻¹)
        ≤ K * ε ^ (((d : ℝ) * k)⁻¹) * (2 * r) ^ d

/-! ### One variable -/

theorem const_fun_eq {x : Fin 1 → ℝ} : (fun _ => x default : Fin 1 → ℝ) = x := by
  funext j
  congr 1
  exact Subsingleton.elim _ _

theorem volume_eq_of_funUnique {s : Set (Fin 1 → ℝ)} (hs : MeasurableSet s) :
    volume s = volume {t : ℝ | (fun _ => t : Fin 1 → ℝ) ∈ s} := by
  have hcont : Continuous fun t : ℝ => (fun _ => t : Fin 1 → ℝ) :=
    continuous_pi fun _ => continuous_id
  have hs' : MeasurableSet {t : ℝ | (fun _ => t : Fin 1 → ℝ) ∈ s} := hcont.measurable hs
  have hpre : (⇑(MeasurableEquiv.funUnique (Fin 1) ℝ)) ⁻¹'
      {t : ℝ | (fun _ => t : Fin 1 → ℝ) ∈ s} = s := by
    ext x
    show (fun _ => x default : Fin 1 → ℝ) ∈ s ↔ x ∈ s
    rw [const_fun_eq]
  calc volume s = volume ((⇑(MeasurableEquiv.funUnique (Fin 1) ℝ)) ⁻¹'
        {t : ℝ | (fun _ => t : Fin 1 → ℝ) ∈ s}) := by rw [hpre]
    _ = volume {t : ℝ | (fun _ => t : Fin 1 → ℝ) ∈ s} :=
        (volume_preserving_funUnique (Fin 1) ℝ).measure_preimage hs'.nullMeasurableSet

theorem mem_ball_one {x₀ : Fin 1 → ℝ} {r t : ℝ} (hr : 0 < r) :
    (fun _ => t : Fin 1 → ℝ) ∈ ball x₀ r ↔ t ∈ Ioo (x₀ 0 - r) (x₀ 0 + r) := by
  rw [ball_pi _ hr]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Real.ball_eq_Ioo]
  constructor
  · intro h; exact h 0
  · intro h j
    have : j = 0 := Subsingleton.elim _ _
    rw [this]
    exact h

/-- **Lemma 3.3 in one variable.**  A function with a sandwiched coordinate chain satisfies the
cube estimate in dimension one. -/
theorem cubeEstimate_one {k : ℕ} (hk : 1 ≤ k) {A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 < A₂) :
    ∃ K : ℝ, 0 < K ∧ CubeEstimate 1 k A₁ A₂ K := by
  obtain ⟨C, hCpos, hC⟩ := exists_good_const_one_dim k hk hA₁ hA₂
  refine ⟨C, hCpos, ?_⟩
  intro V f H x₀ r hr hsub ε hε z hz
  obtain ⟨F, hF0, hFc, hFb⟩ := H.chain 0 z
  have hupd : ∀ t : ℝ, Function.update z 0 t = (fun _ => t : Fin 1 → ℝ) := by
    intro t
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hj]
    simp
  set a : ℝ := x₀ 0 - r with ha
  set b : ℝ := x₀ 0 + r with hb
  have hab : a < b := by rw [ha, hb]; linarith
  have hIsub : Ioo a b ⊆ {t | Function.update z 0 t ∈ V} := by
    intro t ht
    show Function.update z 0 t ∈ V
    rw [hupd]
    exact hsub ((mem_ball_one hr).mpr ht)
  have hFc' : IsDerivChain F {t | Function.update z 0 t ∈ V} := hFc
  have hchain : IsDerivChain F (Ioo a b) := hFc'.mono hIsub
  have hup : ∀ t ∈ Ioo a b, |F k t| ≤ A₁ := fun t ht => (hFb t (hIsub ht)).1
  have hlow : ∀ t ∈ Ioo a b, A₂ ≤ |F k t| := fun t ht => (hFb t (hIsub ht)).2
  have hz0 : z 0 ∈ Ioo a b := by
    have : (fun _ => z 0 : Fin 1 → ℝ) ∈ ball x₀ r := by
      rw [← hupd (z 0), Function.update_eq_self]
      exact hz
    exact (mem_ball_one hr).mp this
  have hmain := hC (Ioo a b) F ordConnected_Ioo hchain hup hlow a b hab (subset_refl _) ε hε
    (z 0) hz0
  -- transfer the measure to the line
  have hmeas : MeasurableSet {x ∈ ball x₀ r | |f x| < ε} :=
    (isOpen_sublevel H.cont hsub).measurableSet
  have hsets : {t : ℝ | (fun _ => t : Fin 1 → ℝ) ∈ {x ∈ ball x₀ r | |f x| < ε}}
      = {t ∈ Ioo a b | |F 0 t| < ε} := by
    ext t
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_ball_one hr).mp h1, by rwa [hF0, hupd]⟩
    · rintro ⟨h1, h2⟩
      rw [hF0, hupd] at h2
      exact ⟨(mem_ball_one hr).mpr h1, h2⟩
  have hvol : volume {x ∈ ball x₀ r | |f x| < ε} = volume {t ∈ Ioo a b | |F 0 t| < ε} := by
    rw [volume_eq_of_funUnique hmeas, hsets]
  have hfz : F 0 (z 0) = f z := by rw [hF0, Function.update_eq_self]
  rw [hvol]
  rw [hfz] at hmain
  have hcast : ((1 : ℕ) : ℝ) * (k : ℝ) = (k : ℝ) := by norm_num
  rw [hcast, pow_one]
  have hba : b - a = 2 * r := by rw [ha, hb]; ring
  rw [hba] at hmain
  linarith [hmain]

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
