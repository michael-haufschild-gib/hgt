import GaloisForLFunctions.HTGeometry.ConstitutiveFormationDepthCompactness
import GaloisForLFunctions.HTGeometry.BoundedFormationRecoveryRigidity
import GaloisForLFunctions.HTGeometry.CompactOperatorRangeMeagre
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Formation-depth Baire-category escape

Let `H = ℓ²(ℕ, ℂ)` and let `D` be the space of histories `x ∈ ℓ¹` with `∑ n |x n| < ∞`
weighted by the depth `n`, normed by the formation gauge
`G(x) = |M(x)| + 2 W(x)`, `M(x) = ∑ x n`, `W(x) = ∑ n |x n|`.

* `(D, G)` is a separable Banach space (hence Polish), and `G` is equivalent to the weighted
  `ℓ¹` norm `W₀(x) = |x 0| + ∑_{n ≥ 1} n |x n|`.
* The canonical inclusion `j : (D, G) → H` is continuous, injective and compact, with dense
  proper range.
* As a subset of `H`, `D = ⋃ N, {G ≤ N}` is dense, proper, σ-compact, `F_σ`, Borel and meagre.
* The codiagonal `M` is continuous on `(D, G)`, but along any sequence with `j xₖ → 0` and
  `M xₖ → c ≠ 0` the gauge escapes to infinity.  Quantitatively
  `|M x| ≤ √N ‖j x‖ + G(x) / (2N)` for every `N ≥ 1`.  The uniform shells
  `u_N = N⁻¹ ∑_{n=1}^N e_n` have `‖j u_N‖ = N^{-1/2}`, `M u_N = 1`, `G u_N = N + 2`, so `M` is
  not sequentially closable relative to `j`.
-/

open scoped BigOperators ENNReal
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The observer completion and the `ℓ¹ → ℓ²` inclusion -/

/-- The observer Hilbert completion `ℓ²(ℕ, ℂ)`. -/
abbrev FormationL2 := lp (fun _ : ℕ => ℂ) 2

theorem memℓp_two_of_formationL1 (x : FormationL1) : Memℓp (x : ℕ → ℂ) 2 :=
  (lp.memℓp x).of_exponent_ge (by norm_num)

/-- The `ℓ²` norm of an `ℓ¹` history is at most its `ℓ¹` norm. -/
theorem norm_formationL1_toL2_le (x : FormationL1) :
    ‖(⟨(x : ℕ → ℂ), memℓp_two_of_formationL1 x⟩ : FormationL2)‖ ≤ ‖x‖ := by
  apply lp.norm_le_of_forall_sum_le (p := 2) (by norm_num) (norm_nonneg x)
  intro s
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  simp only [h2, Real.rpow_natCast]
  have hsum : ∑ i ∈ s, ‖x i‖ ≤ ‖x‖ := by
    rw [formationL1_norm_eq_tsum_norm]
    exact (formationL1_summable x).norm.sum_le_tsum s (fun _ _ => norm_nonneg _)
  calc
    ∑ i ∈ s, ‖x i‖ ^ 2 ≤ (∑ i ∈ s, ‖x i‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
    _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hsum 2

/-- The canonical inclusion `ℓ¹ → ℓ²`, of norm at most one. -/
def formationL1ToL2 : FormationL1 →L[ℂ] FormationL2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨(x : ℕ → ℂ), memℓp_two_of_formationL1 x⟩
      map_add' := fun x y => lp.ext (by simp)
      map_smul' := fun a x => lp.ext (by simp) }
    1 (fun x => by simpa using norm_formationL1_toL2_le x)

@[simp] theorem formationL1ToL2_apply (x : FormationL1) (n : ℕ) :
    (formationL1ToL2 x : ℕ → ℂ) n = x n := rfl

theorem norm_formationL1ToL2_le (x : FormationL1) : ‖formationL1ToL2 x‖ ≤ ‖x‖ :=
  norm_formationL1_toL2_le x

theorem formationL1ToL2_injective : Function.Injective formationL1ToL2 := by
  intro x y h
  apply lp.ext
  funext n
  have := congrArg (fun z : FormationL2 => (z : ℕ → ℂ) n) h
  simpa using this

/-- The observer completion is infinite dimensional. -/
theorem not_finiteDimensional_formationL2 : ¬ FiniteDimensional ℂ FormationL2 := by
  intro h
  exact Module.Finite.not_linearIndependent_of_infinite _
    ((default : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2)).orthonormal.linearIndependent)

/-! ## Algebra of the formation gauge -/

theorem formationDepthSequence_add (f g : ℕ → ℂ) :
    formationDepthSequence (f + g) = formationDepthSequence f + formationDepthSequence g := by
  funext n
  simp [formationDepthSequence, mul_add]

theorem formationDepthSequence_sub (f g : ℕ → ℂ) :
    formationDepthSequence (f - g) = formationDepthSequence f - formationDepthSequence g := by
  funext n
  simp [formationDepthSequence, mul_sub]

theorem formationMass_add {f g : ℕ → ℂ} (hf : Summable f) (hg : Summable g) :
    formationMass (f + g) = formationMass f + formationMass g := by
  simp only [formationMass, Pi.add_apply]
  exact hf.tsum_add hg

theorem formationDepthWork_nonneg (f : ℕ → ℂ) : 0 ≤ formationDepthWork f :=
  tsum_nonneg fun _ => norm_nonneg _

theorem formationDepthWork_add_le {f g : ℕ → ℂ}
    (hf : Summable (formationDepthSequence f)) (hg : Summable (formationDepthSequence g)) :
    formationDepthWork (f + g) ≤ formationDepthWork f + formationDepthWork g := by
  unfold formationDepthWork
  rw [formationDepthSequence_add]
  calc
    ∑' n, ‖(formationDepthSequence f + formationDepthSequence g) n‖ ≤
        ∑' n, (‖formationDepthSequence f n‖ + ‖formationDepthSequence g n‖) :=
      Summable.tsum_le_tsum (fun n => norm_add_le _ _) (hf.add hg).norm
        (hf.norm.add hg.norm)
    _ = _ := hf.norm.tsum_add hg.norm

/-- The formation gauge is subadditive on the graph domain. -/
theorem formationGauge_add_le {f g : ℕ → ℂ} (hf : Summable f) (hg : Summable g)
    (hDf : Summable (formationDepthSequence f)) (hDg : Summable (formationDepthSequence g)) :
    formationGauge (f + g) ≤ formationGauge f + formationGauge g := by
  unfold formationGauge
  rw [formationMass_add hf hg]
  have h1 := norm_add_le (formationMass f) (formationMass g)
  have h2 := formationDepthWork_add_le hDf hDg
  linarith

/-- The codiagonal is bounded by the absolute mass. -/
theorem norm_formationMass_le_tsum_norm {f : ℕ → ℂ} (hf : Summable f) :
    ‖formationMass f‖ ≤ ∑' n, ‖f n‖ :=
  norm_tsum_le_tsum_norm hf.norm

/-- Upper comparison of the gauge with absolute mass plus depth work. -/
theorem formationGauge_le_tsum_norm_add {f : ℕ → ℂ} (hf : Summable f) :
    formationGauge f ≤ (∑' n, ‖f n‖) + 2 * formationDepthWork f := by
  unfold formationGauge
  have := norm_formationMass_le_tsum_norm hf
  linarith

theorem norm_natCast_add_one (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  exact_mod_cast Complex.norm_natCast (n + 1)

/-- Depth work is the weighted sum over positive depths: `W(x) = ∑_{n ≥ 1} n |x n|`. -/
theorem formationDepthWork_eq_tsum_succ {f : ℕ → ℂ}
    (hDf : Summable (formationDepthSequence f)) :
    formationDepthWork f = ∑' n, ((n + 1 : ℕ) : ℝ) * ‖f (n + 1)‖ := by
  unfold formationDepthWork
  rw [← hDf.norm.sum_add_tsum_nat_add 1]
  simp [formationDepthSequence, norm_natCast_add_one]

/-- Tail mass is controlled by depth work: `∑_{n ≥ 1} |x n| ≤ W(x)`. -/
theorem tsum_norm_succ_le_formationDepthWork {f : ℕ → ℂ} (hf : Summable f)
    (hDf : Summable (formationDepthSequence f)) :
    (∑' n, ‖f (n + 1)‖) ≤ formationDepthWork f := by
  rw [formationDepthWork_eq_tsum_succ hDf]
  have hDsucc : Summable (fun n => ((n + 1 : ℕ) : ℝ) * ‖f (n + 1)‖) := by
    have h := (summable_nat_add_iff 1).2 hDf.norm
    simpa [formationDepthSequence, norm_natCast_add_one] using h
  apply Summable.tsum_le_tsum _ ((summable_nat_add_iff 1).2 hf.norm) hDsucc
  intro n
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith [norm_nonneg (f (n + 1))]

/-- The standard weighted `ℓ¹` norm `W₀(x) = |x 0| + ∑_{n ≥ 1} n |x n|`. -/
def formationWeightedNorm (f : ℕ → ℂ) : ℝ :=
  ‖f 0‖ + ∑' n, ((n + 1 : ℕ) : ℝ) * ‖f (n + 1)‖

/-- `W₀ ≤ (3/2) G` on the graph domain. -/
theorem formationWeightedNorm_le_formationGauge {f : ℕ → ℂ} (hf : Summable f)
    (hDf : Summable (formationDepthSequence f)) :
    formationWeightedNorm f ≤ (3 / 2) * formationGauge f := by
  unfold formationWeightedNorm
  rw [← formationDepthWork_eq_tsum_succ hDf]
  have h0 : ‖f 0‖ ≤ ∑' n, ‖f n‖ := by
    simpa using hf.norm.sum_le_tsum {0} (fun _ _ => norm_nonneg _)
  have hG := tsum_norm_le_formationGauge f hf hDf
  have hW : 2 * formationDepthWork f ≤ formationGauge f := by
    unfold formationGauge
    have := norm_nonneg (formationMass f)
    linarith
  linarith

/-- `G ≤ 3 W₀` on the graph domain. -/
theorem formationGauge_le_formationWeightedNorm {f : ℕ → ℂ} (hf : Summable f)
    (hDf : Summable (formationDepthSequence f)) :
    formationGauge f ≤ 3 * formationWeightedNorm f := by
  unfold formationWeightedNorm
  rw [← formationDepthWork_eq_tsum_succ hDf]
  have hsplit : (∑' n, ‖f n‖) = ‖f 0‖ + ∑' n, ‖f (n + 1)‖ := by
    simpa using (hf.norm.sum_add_tsum_nat_add 1).symm
  have htail := tsum_norm_succ_le_formationDepthWork hf hDf
  have hG := formationGauge_le_tsum_norm_add hf
  have hW := formationDepthWork_nonneg f
  have h0 := norm_nonneg (f 0)
  linarith

/-! ## The formation-depth source space `(D, G)` -/

/-- The graph domain of the depth generator as a linear subspace of `ℓ¹`. -/
def formationDepthSubmodule : Submodule ℂ FormationL1 where
  carrier := {x | Summable (formationDepthSequence (x : ℕ → ℂ))}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, lp.coeFn_add, formationDepthSequence_add] at hx hy ⊢
    exact hx.add hy
  zero_mem' := by
    simp only [Set.mem_setOf_eq, lp.coeFn_zero]
    have : formationDepthSequence (0 : ℕ → ℂ) = 0 := by
      funext n
      simp [formationDepthSequence]
    rw [this]
    exact summable_zero
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq, lp.coeFn_smul] at hx ⊢
    have : formationDepthSequence (a • (x : ℕ → ℂ)) =
        fun n => a * formationDepthSequence (x : ℕ → ℂ) n := by
      funext n
      simp only [formationDepthSequence, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    exact hx.mul_left a

theorem mem_formationDepthSubmodule {x : FormationL1} :
    x ∈ formationDepthSubmodule ↔ Summable (formationDepthSequence (x : ℕ → ℂ)) :=
  Iff.rfl

/-- The formation-depth source space `D`, a type synonym for the graph domain that carries the
formation gauge as its norm. -/
def FormationDepthSpace : Type := ↥formationDepthSubmodule

namespace FormationDepthSpace

instance : AddCommGroup FormationDepthSpace :=
  inferInstanceAs (AddCommGroup ↥formationDepthSubmodule)

instance : Module ℂ FormationDepthSpace :=
  inferInstanceAs (Module ℂ ↥formationDepthSubmodule)

/-- The underlying `ℓ¹` history. -/
def toL1 (x : FormationDepthSpace) : FormationL1 :=
  Subtype.val (p := fun y => y ∈ formationDepthSubmodule) x

/-- The coordinates of a source history. -/
def seq (x : FormationDepthSpace) : ℕ → ℂ := (toL1 x : ℕ → ℂ)

theorem summable_seq (x : FormationDepthSpace) : Summable (seq x) :=
  formationL1_summable (toL1 x)

theorem summable_depth (x : FormationDepthSpace) : Summable (formationDepthSequence (seq x)) :=
  Subtype.property (p := fun y => y ∈ formationDepthSubmodule) x

theorem toL1_injective : Function.Injective toL1 := fun _ _ h => Subtype.ext h

theorem ext {x y : FormationDepthSpace} (h : seq x = seq y) : x = y :=
  toL1_injective (lp.ext h)

theorem toL1_add (x y : FormationDepthSpace) : toL1 (x + y) = toL1 x + toL1 y := rfl

theorem toL1_smul (a : ℂ) (x : FormationDepthSpace) : toL1 (a • x) = a • toL1 x := rfl

theorem toL1_sub (x y : FormationDepthSpace) : toL1 (x - y) = toL1 x - toL1 y := rfl

theorem toL1_neg (x : FormationDepthSpace) : toL1 (-x) = -toL1 x := rfl

theorem toL1_zero : toL1 0 = 0 := rfl

theorem seq_add (x y : FormationDepthSpace) : seq (x + y) = seq x + seq y := rfl

theorem seq_smul (a : ℂ) (x : FormationDepthSpace) :
    seq (a • x) = fun n => a * seq x n := by
  funext n
  simp [seq, toL1_smul]

theorem seq_sub (x y : FormationDepthSpace) : seq (x - y) = seq x - seq y := rfl

theorem seq_neg (x : FormationDepthSpace) : seq (-x) = fun n => (-1 : ℂ) * seq x n := by
  funext n
  simp [seq, toL1_neg]

theorem seq_zero : seq 0 = 0 := rfl

/-- The depth generator as a linear map `D → ℓ¹`. -/
def toL1Linear : FormationDepthSpace →ₗ[ℂ] FormationL1 where
  toFun := toL1
  map_add' := toL1_add
  map_smul' := toL1_smul

/-- A history vanishing from depth `N` on, as a source history. -/
def ofFiniteSupport (f : ℕ → ℂ) (N : ℕ) (hf : ∀ n, N ≤ n → f n = 0) : FormationDepthSpace :=
  let hfin : Set.Finite {n | f n ≠ 0} :=
    (Set.finite_lt_nat N).subset fun n hn => by
      by_contra hlt
      exact hn (hf n (not_lt.1 hlt))
  let x : FormationL1 := ⟨f, (memℓp_zero hfin).of_exponent_ge (by simp)⟩
  ⟨x, show Summable (formationDepthSequence f) from
    summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp [formationDepthSequence, hf n hn]⟩

@[simp] theorem seq_ofFiniteSupport (f : ℕ → ℂ) (N : ℕ) (hf : ∀ n, N ≤ n → f n = 0) :
    seq (ofFiniteSupport f N hf) = f := rfl

/-! ### The formation gauge as a norm -/

/-- The formation gauge `G(x) = |M(x)| + 2 W(x)` of a source history. -/
def gauge (x : FormationDepthSpace) : ℝ := formationGauge (seq x)

theorem gauge_add_le (x y : FormationDepthSpace) : gauge (x + y) ≤ gauge x + gauge y := by
  unfold gauge
  rw [seq_add]
  exact formationGauge_add_le (summable_seq x) (summable_seq y) (summable_depth x)
    (summable_depth y)

theorem gauge_smul (a : ℂ) (x : FormationDepthSpace) : gauge (a • x) = ‖a‖ * gauge x := by
  unfold gauge
  rw [seq_smul, formationGauge_smul]

theorem gauge_neg (x : FormationDepthSpace) : gauge (-x) = gauge x := by
  unfold gauge
  rw [seq_neg, formationGauge_smul]
  simp

theorem gauge_zero : gauge 0 = 0 := by
  unfold gauge
  rw [seq_zero]
  simp [formationGauge, formationMass, formationDepthWork, formationDepthSequence]

theorem eq_zero_of_gauge_eq_zero {x : FormationDepthSpace} (hx : gauge x = 0) : x = 0 := by
  apply ext
  rw [seq_zero]
  exact (formationGauge_eq_zero_iff _ (summable_seq x) (summable_depth x)).1 hx

/-- The formation gauge is a group norm on `D`. -/
def gaugeAddGroupNorm : AddGroupNorm FormationDepthSpace where
  toFun := gauge
  map_zero' := gauge_zero
  add_le' := gauge_add_le
  neg' := gauge_neg
  eq_zero_of_map_eq_zero' := fun _ hx => eq_zero_of_gauge_eq_zero hx

instance : NormedAddCommGroup FormationDepthSpace :=
  gaugeAddGroupNorm.toNormedAddCommGroup

theorem norm_def (x : FormationDepthSpace) : ‖x‖ = formationGauge (seq x) := rfl

instance : NormedSpace ℂ FormationDepthSpace where
  norm_smul_le a x := le_of_eq (gauge_smul a x)

/-- **`G` is a norm on `D`.**  The norm of the source space is literally the formation gauge; it is
definite, subadditive and absolutely homogeneous. -/
theorem formationGauge_isNorm :
    (∀ x : FormationDepthSpace, ‖x‖ = formationGauge (seq x)) ∧
      (∀ x : FormationDepthSpace, ‖x‖ = 0 ↔ x = 0) ∧
      (∀ x y : FormationDepthSpace, ‖x + y‖ ≤ ‖x‖ + ‖y‖) ∧
      (∀ (a : ℂ) (x : FormationDepthSpace), ‖a • x‖ = ‖a‖ * ‖x‖) :=
  ⟨norm_def, fun _ => norm_eq_zero, norm_add_le, fun a x => gauge_smul a x⟩

/-- **Norm equivalence with the weighted `ℓ¹` norm:** `W₀ ≤ (3/2) G` and `G ≤ 3 W₀`. -/
theorem formationWeightedNorm_equivalent (x : FormationDepthSpace) :
    formationWeightedNorm (seq x) ≤ (3 / 2) * ‖x‖ ∧ ‖x‖ ≤ 3 * formationWeightedNorm (seq x) :=
  ⟨formationWeightedNorm_le_formationGauge (summable_seq x) (summable_depth x),
    formationGauge_le_formationWeightedNorm (summable_seq x) (summable_depth x)⟩

/-- The `ℓ¹` norm is dominated by the gauge. -/
theorem norm_toL1_le (x : FormationDepthSpace) : ‖toL1 x‖ ≤ ‖x‖ := by
  rw [formationL1_norm_eq_tsum_norm]
  exact tsum_norm_le_formationGauge _ (summable_seq x) (summable_depth x)

/-- The continuous inclusion `(D, G) → ℓ¹`. -/
def toL1CLM : FormationDepthSpace →L[ℂ] FormationL1 :=
  toL1Linear.mkContinuous 1 (fun x => by simpa [toL1Linear] using norm_toL1_le x)

@[simp] theorem toL1CLM_apply (x : FormationDepthSpace) : toL1CLM x = toL1 x := rfl

/-- The source history lies in the `ℓ¹` gauge sublevel of its own norm. -/
theorem toL1_mem_formationLpGaugeSublevel (x : FormationDepthSpace) {C : ℝ} (hC : ‖x‖ ≤ C) :
    toL1 x ∈ formationLpGaugeSublevel C :=
  ⟨summable_depth x, hC⟩

/-! ### Completeness -/

instance : CompleteSpace FormationDepthSpace := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hv : CauchySeq (fun n => toL1 (u n)) :=
    toL1CLM.uniformContinuous.comp_cauchySeq hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hv
  have key : ∀ ε > 0, ∃ N, ∀ n ≥ N, toL1 (u n) - y ∈ formationLpGaugeSublevel ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hlim : Tendsto (fun m => toL1 (u n) - toL1 (u m)) atTop (𝓝 (toL1 (u n) - y)) :=
      tendsto_const_nhds.sub hy
    apply (isClosed_formationLpGaugeSublevel ε).mem_of_tendsto hlim
    filter_upwards [eventually_ge_atTop N] with m hm
    rw [← toL1_sub]
    apply toL1_mem_formationLpGaugeSublevel
    rw [← dist_eq_norm]
    exact (hN n hn m hm).le
  obtain ⟨N₀, hN₀⟩ := key 1 one_pos
  have hyD : Summable (formationDepthSequence (y : ℕ → ℂ)) := by
    have h1 : Summable (formationDepthSequence ((toL1 (u N₀) - y : FormationL1) : ℕ → ℂ)) :=
      (hN₀ N₀ le_rfl).1
    have h2 : Summable (formationDepthSequence (seq (u N₀))) := summable_depth (u N₀)
    have h3 := h2.sub h1
    have heq : formationDepthSequence (y : ℕ → ℂ) =
        fun n => formationDepthSequence (seq (u N₀)) n -
          formationDepthSequence ((toL1 (u N₀) - y : FormationL1) : ℕ → ℂ) n := by
      funext n
      simp [formationDepthSequence, seq, mul_sub]
    rw [heq]
    exact h3
  let a : FormationDepthSpace := ⟨y, hyD⟩
  have ha : toL1 a = y := rfl
  refine ⟨a, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := key (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, norm_def]
  have hmem := hN n hn
  have hle : formationLpGauge (toL1 (u n) - y) ≤ ε / 2 := hmem.2
  have hseq : seq (u n - a) = ((toL1 (u n) - y : FormationL1) : ℕ → ℂ) := by
    simp [seq, toL1_sub, ha]
  rw [hseq]
  change formationLpGauge (toL1 (u n) - y) < ε
  linarith

/-! ### Separability -/

/-- Coordinate heads of depth `N` as source histories. -/
def headLinear (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] FormationDepthSpace where
  toFun v := ofFiniteSupport (fun n => if h : n < N then v ⟨n, h⟩ else 0) N
    (fun n hn => by simp [not_lt.2 hn])
  map_add' v w := by
    apply ext
    funext n
    simp only [seq_ofFiniteSupport, seq_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' a v := by
    apply ext
    funext n
    simp only [seq_ofFiniteSupport, seq_smul, RingHom.id_apply]
    split_ifs <;> simp

theorem seq_headLinear (N : ℕ) (v : Fin N → ℂ) (n : ℕ) :
    seq (headLinear N v) n = if h : n < N then v ⟨n, h⟩ else 0 := rfl

/-- Truncation of a source history at depth `N`. -/
def truncate (N : ℕ) (x : FormationDepthSpace) : FormationDepthSpace :=
  headLinear N (fun i => seq x i)

theorem seq_sub_truncate (N : ℕ) (x : FormationDepthSpace) :
    seq (x - truncate N x) = fun n => if n < N then 0 else seq x n := by
  funext n
  rw [seq_sub]
  simp only [Pi.sub_apply, truncate, seq_headLinear]
  split_ifs <;> simp

theorem tsum_eq_tsum_nat_add_of_forall_lt_eq_zero {f : ℕ → ℝ} (N : ℕ) (hf : Summable f)
    (h0 : ∀ n < N, f n = 0) : ∑' n, f n = ∑' k, f (k + N) := by
  rw [← hf.sum_add_tsum_nat_add N,
    Finset.sum_eq_zero (fun n hn => h0 n (Finset.mem_range.1 hn)), zero_add]

/-- Truncation error is bounded by the cofinal mass tail plus the cofinal depth tail. -/
theorem norm_sub_truncate_le (N : ℕ) (x : FormationDepthSpace) :
    ‖x - truncate N x‖ ≤
      (∑' k, ‖seq x (k + N)‖) + 2 * ∑' k, ‖formationDepthSequence (seq x) (k + N)‖ := by
  set z := x - truncate N x with hz
  have hzseq := seq_sub_truncate N x
  rw [norm_def]
  refine (formationGauge_le_tsum_norm_add (summable_seq z)).trans (le_of_eq ?_)
  have hmass : (∑' n, ‖seq z n‖) = ∑' k, ‖seq x (k + N)‖ := by
    rw [tsum_eq_tsum_nat_add_of_forall_lt_eq_zero N (summable_seq z).norm]
    · congr 1
      funext k
      rw [hzseq]
      simp
    · intro n hn
      rw [hzseq]
      simp [hn]
  have hdepth : formationDepthWork (seq z) =
      ∑' k, ‖formationDepthSequence (seq x) (k + N)‖ := by
    unfold formationDepthWork
    rw [tsum_eq_tsum_nat_add_of_forall_lt_eq_zero N (summable_depth z).norm]
    · congr 1
      funext k
      rw [hzseq]
      simp [formationDepthSequence]
    · intro n hn
      rw [hzseq]
      simp [formationDepthSequence, hn]
  rw [hmass, hdepth]

theorem tendsto_truncate (x : FormationDepthSpace) :
    Tendsto (fun N => truncate N x) atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ =>
      (∑' k, ‖seq x (k + N)‖) + 2 * ∑' k, ‖formationDepthSequence (seq x) (k + N)‖)
      atTop (𝓝 0) := by
    have h1 := tendsto_sum_nat_add (fun n => ‖seq x n‖)
    have h2 := tendsto_sum_nat_add (fun n => ‖formationDepthSequence (seq x) n‖)
    simpa using h1.add (h2.const_mul 2)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hlim
  rw [norm_sub_rev]
  exact norm_sub_truncate_le N x

instance : TopologicalSpace.SeparableSpace FormationDepthSpace := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have hsep : TopologicalSpace.IsSeparable (⋃ N : ℕ, Set.range (headLinear N)) :=
    TopologicalSpace.IsSeparable.iUnion fun N =>
      TopologicalSpace.isSeparable_range (LinearMap.continuous_of_finiteDimensional _)
  refine hsep.closure.mono fun x _ => ?_
  exact mem_closure_of_tendsto (tendsto_truncate x)
    (Eventually.of_forall fun N => Set.mem_iUnion.2 ⟨N, ⟨_, rfl⟩⟩)

/-- `(D, G)` is a Polish space. -/
instance : PolishSpace FormationDepthSpace := inferInstance

end FormationDepthSpace

open FormationDepthSpace

/-! ## The canonical inclusion `j : (D, G) → H` -/

/-- The canonical inclusion `j : (D, G) → ℓ²`. -/
def formationDepthInclusion : FormationDepthSpace →L[ℂ] FormationL2 :=
  formationL1ToL2.comp toL1CLM

@[simp] theorem formationDepthInclusion_apply (x : FormationDepthSpace) (n : ℕ) :
    (formationDepthInclusion x : ℕ → ℂ) n = seq x n := rfl

/-- `‖j x‖₂ ≤ ‖x‖₁ ≤ G(x)`. -/
theorem norm_formationDepthInclusion_le (x : FormationDepthSpace) :
    ‖formationDepthInclusion x‖ ≤ ‖toL1 x‖ ∧ ‖toL1 x‖ ≤ ‖x‖ :=
  ⟨norm_formationL1ToL2_le (toL1 x), norm_toL1_le x⟩

theorem formationDepthInclusion_injective : Function.Injective formationDepthInclusion :=
  fun _ _ h => toL1_injective (formationL1ToL2_injective h)

/-- The inclusion maps the closed gauge ball of radius `C` into the compact `ℓ²` image of the
`ℓ¹` gauge sublevel. -/
theorem formationDepthInclusion_closedBall_subset (C : ℝ) :
    Metric.closedBall (0 : FormationDepthSpace) C ⊆
      formationDepthInclusion ⁻¹' (formationL1ToL2 '' formationLpGaugeSublevel C) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  exact ⟨toL1 x, toL1_mem_formationLpGaugeSublevel x hx, rfl⟩

theorem isCompact_formationL1ToL2_image_sublevel (C : ℝ) :
    IsCompact (formationL1ToL2 '' formationLpGaugeSublevel C) :=
  (isCompact_formationLpGaugeSublevel C).image formationL1ToL2.continuous

/-- The inclusion `j` is a compact operator. -/
theorem isCompactOperator_formationDepthInclusion :
    IsCompactOperator formationDepthInclusion :=
  ⟨_, isCompact_formationL1ToL2_image_sublevel 1,
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos)
      (formationDepthInclusion_closedBall_subset 1)⟩

/-- Truncations of an observer vector are included source histories. -/
theorem formationDepthInclusion_truncation (y : FormationL2) (N : ℕ) :
    formationDepthInclusion
        (ofFiniteSupport (fun n => if n < N then y n else 0) N
          (fun n hn => by simp [not_lt.2 hn])) =
      ∑ i ∈ Finset.range N, lp.single 2 i (y i) := by
  apply lp.ext
  funext n
  rw [formationDepthInclusion_apply, seq_ofFiniteSupport, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  rw [Finset.sum_pi_single]
  simp

/-- The inclusion has dense range. -/
theorem denseRange_formationDepthInclusion : DenseRange formationDepthInclusion := by
  intro y
  have hsum := (lp.hasSum_single (p := 2) ENNReal.ofNat_ne_top y).tendsto_sum_nat
  refine mem_closure_of_tendsto hsum (Eventually.of_forall fun N => ?_)
  exact ⟨_, formationDepthInclusion_truncation y N⟩

theorem memℓp_harmonicObserverWitness :
    Memℓp (fun n : ℕ => ((n : ℂ) + 1)⁻¹) 2 := by
  apply memℓp_gen
  have h := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
  refine h.congr fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnorm : ‖((n : ℂ) + 1)⁻¹‖ = ((n : ℝ) + 1)⁻¹ := by
    rw [norm_inv]
    congr 1
    exact_mod_cast Complex.norm_of_nonneg hpos.le
  rw [hnorm, abs_of_pos hpos, one_div, Real.inv_rpow hpos.le]
  norm_num

/-- The harmonic observer vector `(n + 1)⁻¹`: square summable but not summable. -/
def harmonicObserverWitness : FormationL2 :=
  ⟨fun n : ℕ => ((n : ℂ) + 1)⁻¹, memℓp_harmonicObserverWitness⟩

theorem harmonicObserverWitness_not_mem_range :
    harmonicObserverWitness ∉ Set.range formationDepthInclusion := by
  rintro ⟨x, hx⟩
  have hcoord : seq x = fun n : ℕ => ((n : ℂ) + 1)⁻¹ := by
    funext n
    have := congrArg (fun z : FormationL2 => (z : ℕ → ℂ) n) hx
    simpa [harmonicObserverWitness] using this
  have hsum : Summable (fun n : ℕ => ‖((n : ℂ) + 1)⁻¹‖) := by
    have h := (summable_seq x).norm
    rw [hcoord] at h
    exact h
  have hnot := (Real.summable_one_div_nat_add_rpow 1 1).not.2 (by norm_num)
  apply hnot
  refine hsum.congr fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [norm_inv, abs_of_pos hpos, Real.rpow_one, one_div]
  congr 1
  exact_mod_cast Complex.norm_of_nonneg hpos.le

/-- The inclusion has proper range. -/
theorem range_formationDepthInclusion_ne_univ :
    Set.range formationDepthInclusion ≠ Set.univ := fun h =>
  harmonicObserverWitness_not_mem_range (h ▸ Set.mem_univ _)

/-- **Theorem (fine source topology).**  `(D, G)` is a separable Banach space whose norm is the
formation gauge, and the canonical inclusion `j : (D, G) → ℓ²` is continuous, injective and
compact, with dense proper range. -/
theorem formationDepth_fineSourceTopology :
    (∀ x : FormationDepthSpace, ‖x‖ = formationGauge (seq x)) ∧
      CompleteSpace FormationDepthSpace ∧
      TopologicalSpace.SeparableSpace FormationDepthSpace ∧
      Continuous formationDepthInclusion ∧
      Function.Injective formationDepthInclusion ∧
      IsCompactOperator formationDepthInclusion ∧
      DenseRange formationDepthInclusion ∧
      Set.range formationDepthInclusion ≠ Set.univ :=
  ⟨norm_def, inferInstance, inferInstance, formationDepthInclusion.continuous,
    formationDepthInclusion_injective, isCompactOperator_formationDepthInclusion,
    denseRange_formationDepthInclusion, range_formationDepthInclusion_ne_univ⟩

/-! ## The executable core inside the observer completion -/

/-- **Exhaustion:** as a subset of `ℓ²`, `D = ⋃ N, j(K_N)` with `K_N = {G ≤ N}`. -/
theorem range_formationDepthInclusion_eq_iUnion :
    Set.range formationDepthInclusion =
      ⋃ N : ℕ, formationL1ToL2 '' formationLpGaugeSublevel N := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    exact Set.mem_iUnion.2 ⟨N, toL1 x, toL1_mem_formationLpGaugeSublevel x hN, rfl⟩
  · intro hy
    obtain ⟨N, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
    exact ⟨⟨z, hz.1⟩, rfl⟩

theorem isSigmaCompact_range_formationDepthInclusion :
    IsSigmaCompact (Set.range formationDepthInclusion) :=
  ⟨fun N : ℕ => formationL1ToL2 '' formationLpGaugeSublevel N,
    fun N => isCompact_formationL1ToL2_image_sublevel N,
    range_formationDepthInclusion_eq_iUnion.symm⟩

/-- `D` is an `F_σ` subset of `ℓ²`. -/
theorem range_formationDepthInclusion_isFσ :
    ∃ F : ℕ → Set FormationL2, (∀ N, IsClosed (F N)) ∧
      Set.range formationDepthInclusion = ⋃ N, F N :=
  ⟨fun N : ℕ => formationL1ToL2 '' formationLpGaugeSublevel N,
    fun N => (isCompact_formationL1ToL2_image_sublevel N).isClosed,
    range_formationDepthInclusion_eq_iUnion⟩

/-- Equivalently, the complement of `D` is a `G_δ` subset of `ℓ²`. -/
theorem isGδ_compl_range_formationDepthInclusion :
    IsGδ (Set.range formationDepthInclusion)ᶜ := by
  rw [range_formationDepthInclusion_eq_iUnion, Set.compl_iUnion]
  exact IsGδ.iInter_of_isOpen fun N =>
    (isCompact_formationL1ToL2_image_sublevel N).isClosed.isOpen_compl

/-- `D` is a Borel subset of `ℓ²`. -/
theorem measurableSet_range_formationDepthInclusion [MeasurableSpace FormationL2]
    [OpensMeasurableSpace FormationL2] :
    MeasurableSet (Set.range formationDepthInclusion) := by
  rw [range_formationDepthInclusion_eq_iUnion]
  exact MeasurableSet.iUnion fun N =>
    (isCompact_formationL1ToL2_image_sublevel N).isClosed.measurableSet

/-- Every compact gauge sublevel is nowhere dense in `ℓ²`. -/
theorem isNowhereDense_formationL1ToL2_image_sublevel (C : ℝ) :
    IsNowhereDense (formationL1ToL2 '' formationLpGaugeSublevel C) :=
  isNowhereDense_of_isCompact_of_not_finiteDimensional ℂ not_finiteDimensional_formationL2
    (isCompact_formationL1ToL2_image_sublevel C)

/-- `D` is meagre in `ℓ²`. -/
theorem isMeagre_range_formationDepthInclusion :
    IsMeagre (Set.range formationDepthInclusion) := by
  rw [range_formationDepthInclusion_eq_iUnion]
  exact isMeagre_iUnion fun N => (isNowhereDense_formationL1ToL2_image_sublevel N).isMeagre

/-- **Theorem (dense meagre executable core).**  As a subset of `ℓ²`, `D` is dense, proper,
σ-compact, `F_σ` and meagre. -/
theorem formationDepth_denseMeagreCore :
    Dense (Set.range formationDepthInclusion) ∧
      Set.range formationDepthInclusion ≠ Set.univ ∧
      IsSigmaCompact (Set.range formationDepthInclusion) ∧
      (∃ F : ℕ → Set FormationL2, (∀ N, IsClosed (F N)) ∧
        Set.range formationDepthInclusion = ⋃ N, F N) ∧
      IsMeagre (Set.range formationDepthInclusion) :=
  ⟨denseRange_formationDepthInclusion, range_formationDepthInclusion_ne_univ,
    isSigmaCompact_range_formationDepthInclusion, range_formationDepthInclusion_isFσ,
    isMeagre_range_formationDepthInclusion⟩

/-! ## The codiagonal response and its category escape -/

/-- The codiagonal `M(x) = ∑ x n` on the source space. -/
def formationMassLinear : FormationDepthSpace →ₗ[ℂ] ℂ where
  toFun x := formationMass (seq x)
  map_add' x y := by
    rw [seq_add]
    exact formationMass_add (summable_seq x) (summable_seq y)
  map_smul' a x := by
    rw [seq_smul, formationMass_smul]
    rfl

/-- The defining estimate `|M(x)| ≤ G(x)`. -/
theorem norm_formationMass_le_norm (x : FormationDepthSpace) :
    ‖formationMass (seq x)‖ ≤ ‖x‖ := by
  rw [norm_def]
  unfold formationGauge
  have := formationDepthWork_nonneg (seq x)
  linarith

/-- The codiagonal is a continuous functional on `(D, G)`. -/
def formationMassCLM : FormationDepthSpace →L[ℂ] ℂ :=
  formationMassLinear.mkContinuous 1 fun x => by
    simpa [formationMassLinear] using norm_formationMass_le_norm x

@[simp] theorem formationMassCLM_apply (x : FormationDepthSpace) :
    formationMassCLM x = formationMass (seq x) := rfl

/-- The finite head mass is controlled by the observer norm:
`∑_{n < N} |x n| ≤ √N ‖j x‖₂`. -/
theorem sum_range_norm_le_sqrt_mul_norm_inclusion (x : FormationDepthSpace) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖seq x n‖ ≤ Real.sqrt N * ‖formationDepthInclusion x‖ := by
  have hsq : (∑ n ∈ Finset.range N, ‖seq x n‖) ^ 2 ≤ N * ‖formationDepthInclusion x‖ ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun n => ‖seq x n‖)
    rw [Finset.card_range] at hcs
    have hl2 := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) (formationDepthInclusion x)
      (Finset.range N)
    have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
    simp only [h2, Real.rpow_natCast, formationDepthInclusion_apply] at hl2
    calc
      (∑ n ∈ Finset.range N, ‖seq x n‖) ^ 2 ≤ N * ∑ n ∈ Finset.range N, ‖seq x n‖ ^ 2 := hcs
      _ ≤ N * ‖formationDepthInclusion x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg N)
  have hnonneg : 0 ≤ Real.sqrt N * ‖formationDepthInclusion x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  refine abs_le_of_sq_le_sq' ?_ hnonneg |>.2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  exact hsq

/-- **Quantitative category escape.**  For every depth `N ≥ 1`,
`|M(x)| ≤ √N ‖j x‖₂ + G(x) / (2N)`. -/
theorem norm_formationMass_le_sqrt_mul_add_div (x : FormationDepthSpace) {N : ℕ}
    (hN : 0 < N) :
    ‖formationMassCLM x‖ ≤ Real.sqrt N * ‖formationDepthInclusion x‖ + ‖x‖ / (2 * N) := by
  rw [formationMassCLM_apply]
  have hnorm := norm_formationMass_le_tsum_norm (summable_seq x)
  have hsplit := (summable_seq x).norm.sum_add_tsum_nat_add N
  have hhead := sum_range_norm_le_sqrt_mul_norm_inclusion x N
  have htail := formationTail_le_depthWork_div (seq x) (summable_seq x) (summable_depth x) hN
  have hW : formationDepthWork (seq x) ≤ ‖x‖ / 2 := by
    rw [norm_def]
    unfold formationGauge
    have := norm_nonneg (formationMass (seq x))
    linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have htail' : formationTail (seq x) N ≤ ‖x‖ / (2 * N) := by
    calc
      formationTail (seq x) N ≤ formationDepthWork (seq x) / N := htail
      _ ≤ (‖x‖ / 2) / N := div_le_div_of_nonneg_right hW hNreal.le
      _ = ‖x‖ / (2 * N) := by rw [div_div]
  have htailEq : formationTail (seq x) N = ∑' n, ‖seq x (n + N)‖ := rfl
  linarith

/-- **Theorem (response forces category escape).**  If `j xₖ → 0` in `ℓ²` and `M xₖ → c ≠ 0`,
then `G(xₖ) → +∞`. -/
theorem tendsto_norm_atTop_of_inclusion_tendsto_zero_of_mass_tendsto
    {x : ℕ → FormationDepthSpace} {c : ℂ} (hc : c ≠ 0)
    (hj : Tendsto (fun k => formationDepthInclusion (x k)) atTop (𝓝 0))
    (hM : Tendsto (fun k => formationMassCLM (x k)) atTop (𝓝 c)) :
    Tendsto (fun k => ‖x k‖) atTop atTop := by
  rw [tendsto_atTop]
  intro C
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  set C' : ℝ := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C' / ‖c‖)
  have hNpos' : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNpos : 0 < N := by exact_mod_cast hNpos'
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos'
  have hCN : C' / (2 * N) < ‖c‖ / 4 := by
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hcpos).1 hN
    nlinarith
  have hjnorm : Tendsto (fun k => ‖formationDepthInclusion (x k)‖) atTop (𝓝 0) := by
    simpa using hj.norm
  have hjsmall : ∀ᶠ k in atTop, ‖formationDepthInclusion (x k)‖ < ‖c‖ / (4 * Real.sqrt N) :=
    hjnorm.eventually (gt_mem_nhds (by positivity))
  have hMlarge : ∀ᶠ k in atTop, ‖c‖ / 2 < ‖formationMassCLM (x k)‖ :=
    hM.norm.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hjsmall, hMlarge] with k hk1 hk2
  by_contra hlt
  have hlt' : ‖x k‖ < C' := lt_of_lt_of_le (not_le.mp hlt) (le_max_left _ _)
  have hesc := norm_formationMass_le_sqrt_mul_add_div (x k) hNpos
  have h1 : Real.sqrt N * ‖formationDepthInclusion (x k)‖ < ‖c‖ / 4 := by
    have := mul_lt_mul_of_pos_left hk1 hsqrt
    rwa [show Real.sqrt N * (‖c‖ / (4 * Real.sqrt N)) = ‖c‖ / 4 by field_simp] at this
  have h2 : ‖x k‖ / (2 * N) < C' / (2 * N) :=
    div_lt_div_of_pos_right hlt' (by positivity)
  linarith

/-! ### The uniform shells -/

/-- The uniform shell `u_N = N⁻¹ ∑_{n=1}^N e_n`. -/
def formationUniformShell (N : ℕ) : FormationDepthSpace :=
  ofFiniteSupport (fun n => if 1 ≤ n ∧ n ≤ N then (N : ℂ)⁻¹ else 0) (N + 1)
    (fun n hn => by
      have : ¬ (1 ≤ n ∧ n ≤ N) := fun h => by omega
      simp [this])

theorem seq_formationUniformShell (N n : ℕ) :
    seq (formationUniformShell N) n = if 1 ≤ n ∧ n ≤ N then (N : ℂ)⁻¹ else 0 := rfl

/-- Finite-support sums over the shell reduce to the first `N + 1` depths. -/
theorem tsum_formationUniformShell {β : Type*} [AddCommGroup β] [TopologicalSpace β]
    [T2Space β] (F : ℕ → ℂ → β) (hF : ∀ n, F n 0 = 0) (N : ℕ) :
    ∑' n, F n (seq (formationUniformShell N) n) =
      ∑ n ∈ Finset.range N, F (n + 1) (N : ℂ)⁻¹ := by
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · rw [Finset.sum_range_succ']
    simp only [seq_formationUniformShell]
    have h0 : ¬ (1 ≤ 0 ∧ 0 ≤ N) := by omega
    rw [if_neg h0, hF, add_zero]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : 1 ≤ n + 1 ∧ n + 1 ≤ N := by
      have := Finset.mem_range.1 hn
      omega
    rw [if_pos hn']
  · intro n hn
    have : ¬ (1 ≤ n ∧ n ≤ N) := by
      have := Finset.mem_range.not.1 hn
      omega
    simp only [seq_formationUniformShell, if_neg this, hF]

/-- The shell has unit codiagonal: `M(u_N) = 1` for `N ≥ 1`. -/
theorem formationMass_formationUniformShell {N : ℕ} (hN : 0 < N) :
    formationMassCLM (formationUniformShell N) = 1 := by
  rw [formationMassCLM_apply, formationMass]
  rw [tsum_formationUniformShell (fun _ z => z) (fun _ => rfl) N]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- `‖j u_N‖₂² = N⁻¹`. -/
theorem norm_sq_formationDepthInclusion_formationUniformShell (N : ℕ) :
    ‖formationDepthInclusion (formationUniformShell N)‖ ^ 2 = (N : ℝ)⁻¹ := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (formationDepthInclusion (formationUniformShell N))
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  simp only [h2, Real.rpow_natCast, formationDepthInclusion_apply] at h
  rw [h, tsum_formationUniformShell (fun _ z => ‖z‖ ^ 2) (fun _ => by simp) N]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp

/-- `‖j u_N‖₂ = N^{-1/2}`. -/
theorem norm_formationDepthInclusion_formationUniformShell (N : ℕ) :
    ‖formationDepthInclusion (formationUniformShell N)‖ = (Real.sqrt N)⁻¹ := by
  rw [← Real.sqrt_inv, ← norm_sq_formationDepthInclusion_formationUniformShell,
    Real.sqrt_sq (norm_nonneg _)]

/-- Twice the triangular sum: `2 ∑_{n < N} (n + 1) = N (N + 1)`. -/
theorem two_mul_sum_range_succ_cast (N : ℕ) :
    2 * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- The shell gauge is `G(u_N) = N + 2` for `N ≥ 1`. -/
theorem norm_formationUniformShell {N : ℕ} (hN : 0 < N) :
    ‖formationUniformShell N‖ = N + 2 := by
  rw [norm_def, formationGauge]
  have hmass : formationMass (seq (formationUniformShell N)) = 1 :=
    formationMass_formationUniformShell hN
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hwork : formationDepthWork (seq (formationUniformShell N)) = ((N : ℝ) + 1) / 2 := by
    unfold formationDepthWork formationDepthSequence
    rw [tsum_formationUniformShell (fun n z => ‖(n : ℂ) * z‖) (fun _ => by simp) N]
    have hterm : ∀ n ∈ Finset.range N,
        ‖((n + 1 : ℕ) : ℂ) * (N : ℂ)⁻¹‖ = ((n + 1 : ℕ) : ℝ) * (N : ℝ)⁻¹ := by
      intro n _
      rw [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have htri := two_mul_sum_range_succ_cast N
    field_simp
    linarith
  rw [hmass, hwork, norm_one]
  ring

/-- The shells tend to zero in the observer completion. -/
theorem tendsto_formationDepthInclusion_formationUniformShell :
    Tendsto (fun N => formationDepthInclusion (formationUniformShell N)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_formationDepthInclusion_formationUniformShell]
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- The codiagonal is not sequentially closable relative to the inclusion `j`. -/
theorem not_isSequentiallyClosableBetween_formationMass :
    ¬ RHTower.IsSequentiallyClosableBetween
      ((formationMassCLM : FormationDepthSpace →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ)
      ((formationDepthInclusion : FormationDepthSpace →L[ℂ] FormationL2).toLinearMap.restrictScalars
        ℝ) := by
  intro hclose
  have hj : Tendsto (fun k => formationDepthInclusion (formationUniformShell (k + 1)))
      atTop (𝓝 0) :=
    tendsto_formationDepthInclusion_formationUniformShell.comp (tendsto_add_atTop_nat 1)
  have hM : Tendsto (fun k => formationMassCLM (formationUniformShell (k + 1)))
      atTop (𝓝 1) := by
    have : (fun k => formationMassCLM (formationUniformShell (k + 1))) = fun _ => 1 := by
      funext k
      exact formationMass_formationUniformShell (Nat.succ_pos k)
    rw [this]
    exact tendsto_const_nhds
  have h10 : (1 : ℂ) = 0 :=
    hclose (fun k => formationUniformShell (k + 1)) hj 1 hM
  exact one_ne_zero h10

/-- **Theorem (response forces category escape), full form.**  `M` is continuous on `(D, G)`
with `|M x| ≤ G(x)`; every observer-null sequence with nonzero limiting codiagonal has gauge
tending to infinity; the uniform shells realise this with `‖j u_N‖ = N^{-1/2}`, `M u_N = 1`,
`G u_N = N + 2`; and `M` is not sequentially closable relative to `j`. -/
theorem formationDepth_responseForcesCategoryEscape :
    Continuous formationMassCLM ∧
      (∀ x : FormationDepthSpace, ‖formationMassCLM x‖ ≤ ‖x‖) ∧
      (∀ (x : ℕ → FormationDepthSpace) (c : ℂ), c ≠ 0 →
        Tendsto (fun k => formationDepthInclusion (x k)) atTop (𝓝 0) →
        Tendsto (fun k => formationMassCLM (x k)) atTop (𝓝 c) →
        Tendsto (fun k => ‖x k‖) atTop atTop) ∧
      (∀ N : ℕ, 0 < N →
        ‖formationDepthInclusion (formationUniformShell N)‖ = (Real.sqrt N)⁻¹ ∧
          formationMassCLM (formationUniformShell N) = 1 ∧
          ‖formationUniformShell N‖ = N + 2) ∧
      ¬ RHTower.IsSequentiallyClosableBetween
        ((formationMassCLM : FormationDepthSpace →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ)
        ((formationDepthInclusion :
          FormationDepthSpace →L[ℂ] FormationL2).toLinearMap.restrictScalars ℝ) :=
  ⟨formationMassCLM.continuous, norm_formationMass_le_norm,
    fun _ _ hc hj hM => tendsto_norm_atTop_of_inclusion_tendsto_zero_of_mass_tendsto hc hj hM,
    fun N hN => ⟨norm_formationDepthInclusion_formationUniformShell N,
      formationMass_formationUniformShell hN, norm_formationUniformShell hN⟩,
    not_isSequentiallyClosableBetween_formationMass⟩

end

end GaloisForLFunctions.HTGeometry
