import GaloisForLFunctions.RHTower.BakerProof.MultipointSchwarz

/-!
# A lossless multipoint Schwarz bound for approximate zeros

Let `f` be entire, let `T` be a finite set of nodes and `M ≥ 0`.  With `Ω(z) = ∏_{c ∈ T} (z − c)^M`
and, for each node `x`,

`u_x(z) = Ω_x(z) / Ω_x(x)`,  `Ω_x(z) = ∏_{c ∈ T, c ≠ x} (z − c)^M`,
`E_x(z) = 1 − (1 − u_x(z))^M`,

the polynomial `E_x` equals `1` to order `M` at `x` and vanishes to order `M` at every other node,
because `1 − (1 − u)^M = u · Σ_{i<M} (1 − u)^i`.  Hence the Hermite correction

`H(z) = Σ_{x ∈ T} P_x(z) E_x(z)`,  `P_x` the Taylor polynomial of `f` of order `M` at `x`,

makes `f − H` vanish to order `M` at every node, and the exact multipoint Schwarz bound applied to
`f − H` gives, for `|z| ≤ R`,

`|f(z)| ≤ |H(z)| + |Ω(z)| · sup_{|w|=R} |f − H| / inf_{|w|=R} |Ω|`.

When the first `M` derivatives of `f` at the nodes are at most `ε`, `|P_x(z)| ≤ ε e^{|z−x|}` and
`|E_x| ≤ 2 (1 + |u_x|)^M`, so the correction is `ε` times an explicit factor.  No small circles
around the nodes are used, so nothing of size `ρ^{−M|T|}` enters: the bound is lossless.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Metric

/-- The node polynomial `∏_{c ∈ nodes} (z − c)^M`. -/
def hermiteNodePoly (nodes : Finset ℂ) (M : ℕ) (z : ℂ) : ℂ := ∏ c ∈ nodes, (z - c) ^ M

/-- The Taylor polynomial of order `M` of `f` at `x`. -/
def taylorPolyAt (f : ℂ → ℂ) (x : ℂ) (M : ℕ) (z : ℂ) : ℂ :=
  ∑ t ∈ range M, iteratedDeriv t f x / (t.factorial : ℂ) * (z - x) ^ t

/-- The normalized node polynomial of the other nodes, equal to `1` at `x`. -/
def hermiteRatio (nodes : Finset ℂ) (M : ℕ) (x z : ℂ) : ℂ :=
  hermiteNodePoly (nodes.erase x) M z / hermiteNodePoly (nodes.erase x) M x

/-- The Hermite idempotent of the node `x`. -/
def hermiteIdempotent (nodes : Finset ℂ) (M : ℕ) (x z : ℂ) : ℂ :=
  1 - (1 - hermiteRatio nodes M x z) ^ M

/-- The Hermite correction of `f` at the nodes. -/
def hermiteCorrection (f : ℂ → ℂ) (nodes : Finset ℂ) (M : ℕ) (z : ℂ) : ℂ :=
  ∑ x ∈ nodes, taylorPolyAt f x M z * hermiteIdempotent nodes M x z

/-! ## Differentiability -/

theorem differentiable_hermiteNodePoly (nodes : Finset ℂ) (M : ℕ) :
    Differentiable ℂ (hermiteNodePoly nodes M) := by
  unfold hermiteNodePoly
  fun_prop

theorem differentiable_taylorPolyAt (f : ℂ → ℂ) (x : ℂ) (M : ℕ) :
    Differentiable ℂ (taylorPolyAt f x M) := by
  unfold taylorPolyAt
  fun_prop

theorem differentiable_hermiteRatio (nodes : Finset ℂ) (M : ℕ) (x : ℂ) :
    Differentiable ℂ (hermiteRatio nodes M x) := by
  unfold hermiteRatio
  exact (differentiable_hermiteNodePoly _ M).div_const _

theorem differentiable_hermiteIdempotent (nodes : Finset ℂ) (M : ℕ) (x : ℂ) :
    Differentiable ℂ (hermiteIdempotent nodes M x) := by
  unfold hermiteIdempotent
  have := differentiable_hermiteRatio nodes M x
  fun_prop

theorem differentiable_hermiteCorrection (f : ℂ → ℂ) (nodes : Finset ℂ) (M : ℕ) :
    Differentiable ℂ (hermiteCorrection f nodes M) := by
  unfold hermiteCorrection
  have h1 := differentiable_taylorPolyAt f
  have h2 := differentiable_hermiteIdempotent nodes M
  fun_prop

/-! ## Orders at the nodes -/

/-- An analytic function vanishing at a point has order at least one there. -/
theorem one_le_analyticOrderAt_of_eq_zero {g : ℂ → ℂ} {y : ℂ} (hg : AnalyticAt ℂ g y)
    (hgy : g y = 0) : (1 : ℕ∞) ≤ analyticOrderAt g y := by
  rw [Order.one_le_iff_ne_zero]
  intro h
  exact ((hg.analyticOrderAt_eq_zero).mp h) hgy

/-- A power `g^M` of a function vanishing at `y` has order at least `M` there. -/
theorem natCast_le_analyticOrderAt_pow {g : ℂ → ℂ} {y : ℂ} (hg : AnalyticAt ℂ g y)
    (hgy : g y = 0) (M : ℕ) : (M : ℕ∞) ≤ analyticOrderAt (g ^ M) y := by
  rw [analyticOrderAt_pow hg]
  calc (M : ℕ∞) = M • (1 : ℕ∞) := by simp
    _ ≤ M • analyticOrderAt g y := by
        exact nsmul_le_nsmul_right (one_le_analyticOrderAt_of_eq_zero hg hgy) M

/-- Multiplying by an analytic function does not lower the order. -/
theorem analyticOrderAt_le_mul_left {g h : ℂ → ℂ} {y : ℂ} (hg : AnalyticAt ℂ g y)
    (hh : AnalyticAt ℂ h y) : analyticOrderAt h y ≤ analyticOrderAt (g * h) y := by
  rw [analyticOrderAt_mul hg hh]
  exact le_add_self

/-- The node polynomial vanishes to order `M` at every node. -/
theorem natCast_le_analyticOrderAt_hermiteNodePoly {nodes : Finset ℂ} {y : ℂ} (hy : y ∈ nodes)
    (M : ℕ) : (M : ℕ∞) ≤ analyticOrderAt (hermiteNodePoly nodes M) y := by
  have hsplit : hermiteNodePoly nodes M =
      (fun z => z - y) ^ M * hermiteNodePoly (nodes.erase y) M := by
    funext z
    simp only [hermiteNodePoly, Pi.mul_apply, Pi.pow_apply]
    rw [← mul_prod_erase nodes (fun c => (z - c) ^ M) hy]
  rw [hsplit, analyticOrderAt_mul (by fun_prop)
    ((differentiable_hermiteNodePoly _ M).analyticAt y)]
  refine le_trans (natCast_le_analyticOrderAt_pow (by fun_prop) (by simp) M) le_self_add

/-- The node polynomial of the other nodes does not vanish at `x`. -/
theorem hermiteNodePoly_erase_ne_zero (nodes : Finset ℂ) (M : ℕ) (x : ℂ) :
    hermiteNodePoly (nodes.erase x) M x ≠ 0 := by
  unfold hermiteNodePoly
  refine prod_ne_zero_iff.mpr fun c hc => pow_ne_zero _ (sub_ne_zero.mpr ?_)
  intro hxc
  exact (mem_erase.mp hc).1 hxc.symm

theorem hermiteRatio_self (nodes : Finset ℂ) (M : ℕ) (x : ℂ) : hermiteRatio nodes M x x = 1 :=
  div_self (hermiteNodePoly_erase_ne_zero nodes M x)

/-- `E_x − 1` vanishes to order `M` at `x`. -/
theorem natCast_le_analyticOrderAt_hermiteIdempotent_sub_one (nodes : Finset ℂ) (M : ℕ)
    (x : ℂ) :
    (M : ℕ∞) ≤ analyticOrderAt (fun z => hermiteIdempotent nodes M x z - 1) x := by
  have hfun : (fun z => hermiteIdempotent nodes M x z - 1) =
      -((fun z => 1 - hermiteRatio nodes M x z) ^ M) := by
    funext z
    simp [hermiteIdempotent]
  rw [hfun, analyticOrderAt_neg]
  have hdiff := differentiable_hermiteRatio nodes M x
  exact natCast_le_analyticOrderAt_pow (((differentiable_const 1).sub hdiff).analyticAt x)
    (by simp [hermiteRatio_self]) M

/-- `E_x` vanishes to order `M` at every other node. -/
theorem natCast_le_analyticOrderAt_hermiteIdempotent {nodes : Finset ℂ} (M : ℕ) {x y : ℂ}
    (hy : y ∈ nodes) (hxy : y ≠ x) :
    (M : ℕ∞) ≤ analyticOrderAt (hermiteIdempotent nodes M x) y := by
  have hdiff := differentiable_hermiteRatio nodes M x
  have hfun : hermiteIdempotent nodes M x =
      (fun z => ∑ i ∈ range M, (1 - hermiteRatio nodes M x z) ^ i) *
        hermiteRatio nodes M x := by
    funext z
    have hg := geom_sum_mul (1 - hermiteRatio nodes M x z) M
    simp only [hermiteIdempotent, Pi.mul_apply]
    linear_combination hg
  rw [hfun]
  have hsumd : Differentiable ℂ fun z => ∑ i ∈ range M, (1 - hermiteRatio nodes M x z) ^ i :=
    Differentiable.fun_sum fun i _ => ((differentiable_const 1).sub hdiff).pow i
  refine le_trans ?_ (analyticOrderAt_le_mul_left (hsumd.analyticAt y) (hdiff.analyticAt y))
  have hratio : hermiteRatio nodes M x =
      (fun _ => (hermiteNodePoly (nodes.erase x) M x)⁻¹) * hermiteNodePoly (nodes.erase x) M := by
    funext z
    simp only [hermiteRatio, Pi.mul_apply]
    rw [div_eq_inv_mul]
  rw [hratio, analyticOrderAt_mul analyticAt_const
    ((differentiable_hermiteNodePoly _ M).analyticAt y)]
  have hconst : analyticOrderAt (fun _ : ℂ => (hermiteNodePoly (nodes.erase x) M x)⁻¹) y = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr
      (inv_ne_zero (hermiteNodePoly_erase_ne_zero nodes M x))
  rw [hconst, zero_add]
  exact natCast_le_analyticOrderAt_hermiteNodePoly (mem_erase.mpr ⟨hxy, hy⟩) M

/-- The derivatives of the Taylor polynomial at its centre are those of `f`. -/
theorem iteratedDeriv_taylorPolyAt (f : ℂ → ℂ) (x : ℂ) {M i : ℕ} (hi : i < M) :
    iteratedDeriv i (taylorPolyAt f x M) x = iteratedDeriv i f x := by
  have hterm : ∀ t : ℕ, iteratedDeriv i
      (fun z => iteratedDeriv t f x / (t.factorial : ℂ) * (z - x) ^ t) x =
      if i = t then iteratedDeriv t f x else 0 := by
    intro t
    rw [iteratedDeriv_const_mul_field]
    have hshift := congrFun (iteratedDeriv_comp_sub_const i (fun w : ℂ => w ^ t) x) x
    rw [hshift, sub_self, iteratedDeriv_fun_pow_zero]
    split_ifs with h
    · subst h
      have hfac : ((i.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
      field_simp
    · simp
  have hsum : taylorPolyAt f x M =
      ∑ t ∈ range M, fun z => iteratedDeriv t f x / (t.factorial : ℂ) * (z - x) ^ t := by
    funext z
    simp [taylorPolyAt]
  rw [hsum, iteratedDeriv_sum (fun t _ => by fun_prop)]
  simp only [hterm]
  rw [sum_ite_eq (range M) i (fun t => iteratedDeriv t f x)]
  simp [mem_range.mpr hi]

/-- `f` minus its Taylor polynomial vanishes to order `M` at the centre. -/
theorem natCast_le_analyticOrderAt_sub_taylorPolyAt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (x : ℂ) (M : ℕ) : (M : ℕ∞) ≤ analyticOrderAt (f - taylorPolyAt f x M) x := by
  have hT := differentiable_taylorPolyAt f x M
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hf.sub hT).analyticAt x)]
  intro i hi
  rw [iteratedDeriv_sub (hf.contDiff.contDiffAt) (hT.contDiff.contDiffAt),
    iteratedDeriv_taylorPolyAt f x hi, sub_self]

/-- A finite sum of functions each vanishing to order `M` vanishes to order `M`. -/
theorem natCast_le_analyticOrderAt_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) {y : ℂ}
    {M : ℕ} (h : ∀ i ∈ s, (M : ℕ∞) ≤ analyticOrderAt (g i) y) :
    (M : ℕ∞) ≤ analyticOrderAt (∑ i ∈ s, g i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [sum_empty, show analyticOrderAt (0 : ℂ → ℂ) y = ⊤ from
        analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall fun _ => rfl)]
      exact le_top
  | insert a s ha ih =>
      rw [sum_insert ha]
      exact le_trans (le_min (h a (mem_insert_self a s))
        (ih fun i hi => h i (mem_insert_of_mem hi))) le_analyticOrderAt_add

/-- **Hermite interpolation of the node jets.**  `f − H` vanishes to order `M` at every node. -/
theorem natCast_le_analyticOrderAt_sub_hermiteCorrection {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {nodes : Finset ℂ} (M : ℕ) {x : ℂ} (hx : x ∈ nodes) :
    (M : ℕ∞) ≤ analyticOrderAt (f - hermiteCorrection f nodes M) x := by
  have hT := differentiable_taylorPolyAt f
  have hE := differentiable_hermiteIdempotent nodes M
  have hsplit : f - hermiteCorrection f nodes M =
      (f - taylorPolyAt f x M) -
        taylorPolyAt f x M * (fun z => hermiteIdempotent nodes M x z - 1) -
        ∑ y ∈ nodes.erase x, taylorPolyAt f y M * hermiteIdempotent nodes M y := by
    funext z
    simp only [hermiteCorrection, Pi.sub_apply, Pi.mul_apply, Finset.sum_apply]
    rw [← add_sum_erase nodes _ hx]
    ring
  rw [hsplit]
  have h1 := natCast_le_analyticOrderAt_sub_taylorPolyAt hf x M
  have h2 : (M : ℕ∞) ≤ analyticOrderAt
      (taylorPolyAt f x M * fun z => hermiteIdempotent nodes M x z - 1) x :=
    le_trans (natCast_le_analyticOrderAt_hermiteIdempotent_sub_one nodes M x)
      (analyticOrderAt_le_mul_left ((hT x M).analyticAt x) (by
        have := hE x
        exact (by fun_prop : Differentiable ℂ fun z => hermiteIdempotent nodes M x z - 1)
          |>.analyticAt x))
  have h3 : (M : ℕ∞) ≤ analyticOrderAt
      (∑ y ∈ nodes.erase x, taylorPolyAt f y M * hermiteIdempotent nodes M y) x := by
    refine natCast_le_analyticOrderAt_sum _ _ fun y hy => ?_
    have hyx : x ≠ y := fun h => (mem_erase.mp hy).1 h.symm
    exact le_trans (natCast_le_analyticOrderAt_hermiteIdempotent M hx hyx)
      (analyticOrderAt_le_mul_left ((hT y M).analyticAt x) ((hE y).analyticAt x))
  exact le_trans (le_min (le_trans (le_min h1 h2) le_analyticOrderAt_sub) h3)
    le_analyticOrderAt_sub

/-! ## The Schwarz bound and the size of the correction -/

/-- **Lossless multipoint Schwarz bound.**  For `|z| ≤ R`,
`|f(z)| ≤ |H(z)| + |Ω(z)| · (sup_{|w|=R} |f − H|) / (inf_{|w|=R} |Ω|)`. -/
theorem norm_le_hermiteSchwarz {f : ℂ → ℂ} (hf : Differentiable ℂ f) (nodes : Finset ℂ)
    (M : ℕ) {R Mφ D : ℝ} (hR : 0 < R) (hD : 0 < D)
    (hbd : ∀ w ∈ sphere (0 : ℂ) R, ‖f w - hermiteCorrection f nodes M w‖ ≤ Mφ)
    (hDlow : ∀ w ∈ sphere (0 : ℂ) R, D ≤ ‖hermiteNodePoly nodes M w‖)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    ‖f z‖ ≤ ‖hermiteCorrection f nodes M z‖ + ‖hermiteNodePoly nodes M z‖ * (Mφ / D) := by
  have hH := differentiable_hermiteCorrection f nodes M
  have hφ := GaloisForLFunctions.RHTower.BakerProof.multipoint_schwarz_bound
    (f - hermiteCorrection f nodes M) (fun w => (hf.sub hH).analyticAt w) nodes M
    (fun c hc => natCast_le_analyticOrderAt_sub_hermiteCorrection hf M hc) hR hD
    (fun w hw => hbd w hw) (fun w hw => hDlow w hw) hz
  have htri : ‖f z‖ ≤ ‖hermiteCorrection f nodes M z‖ + ‖(f - hermiteCorrection f nodes M) z‖ := by
    have := norm_add_le (hermiteCorrection f nodes M z) ((f - hermiteCorrection f nodes M) z)
    simpa using this
  have hnode : ‖∏ c ∈ nodes, (z - c) ^ M‖ = ‖hermiteNodePoly nodes M z‖ := rfl
  rw [hnode] at hφ
  linarith

/-- Small node jets give a small Taylor polynomial. -/
theorem norm_taylorPolyAt_le {f : ℂ → ℂ} {x : ℂ} {M : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ t < M, ‖iteratedDeriv t f x‖ ≤ ε) (z : ℂ) :
    ‖taylorPolyAt f x M z‖ ≤ ε * Real.exp ‖z - x‖ := by
  calc ‖taylorPolyAt f x M z‖
      ≤ ∑ t ∈ range M, ‖iteratedDeriv t f x / (t.factorial : ℂ) * (z - x) ^ t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ range M, ε * (‖z - x‖ ^ t / t.factorial) := by
        refine sum_le_sum fun t ht => ?_
        rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
        have := hsmall t (mem_range.mp ht)
        have hfac : (0 : ℝ) < t.factorial := by exact_mod_cast t.factorial_pos
        calc ‖iteratedDeriv t f x‖ / t.factorial * ‖z - x‖ ^ t
            ≤ ε / t.factorial * ‖z - x‖ ^ t := by gcongr
          _ = ε * (‖z - x‖ ^ t / t.factorial) := by ring
    _ = ε * ∑ t ∈ range M, ‖z - x‖ ^ t / t.factorial := by rw [mul_sum]
    _ ≤ ε * Real.exp ‖z - x‖ :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (norm_nonneg _) M) hε

/-- The Hermite idempotent is at most `2 (1 + |u_x|)^M`. -/
theorem norm_hermiteIdempotent_le (nodes : Finset ℂ) (M : ℕ) (x z : ℂ) :
    ‖hermiteIdempotent nodes M x z‖ ≤ 2 * (1 + ‖hermiteRatio nodes M x z‖) ^ M := by
  unfold hermiteIdempotent
  have h1 : ‖1 - hermiteRatio nodes M x z‖ ≤ 1 + ‖hermiteRatio nodes M x z‖ := by
    have := norm_sub_le (1 : ℂ) (hermiteRatio nodes M x z)
    simpa using this
  have h2 : (1 : ℝ) ≤ (1 + ‖hermiteRatio nodes M x z‖) ^ M :=
    one_le_pow₀ (by linarith [norm_nonneg (hermiteRatio nodes M x z)])
  calc ‖1 - (1 - hermiteRatio nodes M x z) ^ M‖
      ≤ ‖(1 : ℂ)‖ + ‖(1 - hermiteRatio nodes M x z) ^ M‖ := norm_sub_le _ _
    _ ≤ 1 + (1 + ‖hermiteRatio nodes M x z‖) ^ M := by
        rw [norm_one, norm_pow]
        gcongr
    _ ≤ 2 * (1 + ‖hermiteRatio nodes M x z‖) ^ M := by linarith

/-- **Size of the correction.**  With node jets at most `ε`,
`|H(z)| ≤ Σ_x 2 ε e^{|z−x|} (1 + |u_x(z)|)^M`. -/
theorem norm_hermiteCorrection_le {f : ℂ → ℂ} {nodes : Finset ℂ} {M : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : ∀ x ∈ nodes, ∀ t < M, ‖iteratedDeriv t f x‖ ≤ ε) (z : ℂ) :
    ‖hermiteCorrection f nodes M z‖ ≤
      ∑ x ∈ nodes, 2 * ε * Real.exp ‖z - x‖ * (1 + ‖hermiteRatio nodes M x z‖) ^ M := by
  unfold hermiteCorrection
  refine (norm_sum_le _ _).trans (sum_le_sum fun x hx => ?_)
  rw [norm_mul]
  have hT := norm_taylorPolyAt_le hε (hsmall x hx) z
  have hE := norm_hermiteIdempotent_le nodes M x z
  have hTnn : 0 ≤ ‖taylorPolyAt f x M z‖ := norm_nonneg _
  calc ‖taylorPolyAt f x M z‖ * ‖hermiteIdempotent nodes M x z‖
      ≤ (ε * Real.exp ‖z - x‖) * (2 * (1 + ‖hermiteRatio nodes M x z‖) ^ M) :=
        mul_le_mul hT hE (norm_nonneg _) (le_trans hTnn hT)
    _ = 2 * ε * Real.exp ‖z - x‖ * (1 + ‖hermiteRatio nodes M x z‖) ^ M := by ring

end GaloisForLFunctions.RHTower.Matveev
