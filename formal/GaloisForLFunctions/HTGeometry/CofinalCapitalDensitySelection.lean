import GaloisForLFunctions.HTGeometry.FormationCloneRigidityLaw
import Mathlib.Analysis.MeanInequalities

/-!
# Cofinal capital-density selection

Sections 1, 2 and 5 of the formation-resource card `ULF-FRM-4`.

* `(CDS.1)`–`(CDS.6)`  finite binary experiments, their Rényi overlap and extended Rényi capital,
  independent `d`-fold formation, and the source capital density;
* `(CDS.7)`  **Theorem 2.1**: every exact formation array pays the whole formed target capital out
  of source capital, so target capital is bounded by source capital density;
* `(CDS.8)`–`(CDS.10)`  **Theorem 2.2**: vanishing capital density forces vanishing target capital,
  and zero capital is exactly target neutrality (strict AM--GM/Hölder equality);
* `(CDS.11)`, `(CDS.12)`  the coercivity conversion into a quantitative displacement bound;
* `(CDS.22)`, `(CDS.23)`  **Theorem 5.1** and **Corollary 5.2**: capital is a Blackwell invariant
  and independent formation multiplies it exactly, so sufficient recovery saturates capital density
  rather than selecting.

Everything is unconditional and finite.
-/

open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X Y S : Type*}

/-- `(CDS.5)` Rényi overlap of two finite packets at order `α`. -/
def renyiOverlap [Fintype X] (α : ℝ) (u v : X → ℝ) : ℝ :=
  ∑ x, u x ^ α * v x ^ (1 - α)

/-- `(CDS.5)` Extended Rényi capital: `-log` of the overlap, with value `∞` when the overlap
degenerates. -/
def renyiCapital [Fintype X] (α : ℝ) (u v : X → ℝ) : ℝ≥0∞ :=
  if 0 < renyiOverlap α u v then ENNReal.ofReal (-Real.log (renyiOverlap α u v)) else ⊤

theorem renyiOverlap_nonneg [Fintype X] {α : ℝ} {u v : X → ℝ}
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) : 0 ≤ renyiOverlap α u v :=
  Finset.sum_nonneg fun x _ =>
    mul_nonneg (Real.rpow_nonneg (hu x) _) (Real.rpow_nonneg (hv x) _)

/-- Pointwise weighted arithmetic--geometric bound behind every Rényi estimate. -/
theorem renyi_pointwise_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ α * b ^ (1 - α) ≤ α * a + (1 - α) * b := by
  have := Real.geom_mean_le_arith_mean2_weighted h0 (by linarith : (0:ℝ) ≤ 1 - α) ha hb
    (by ring)
  exact this

/-- `(CDS.5)` For probability packets the overlap is at most one. -/
theorem renyiOverlap_le_one [Fintype X] {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {u v : X → ℝ}
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hu1 : ∑ x, u x = 1) (hv1 : ∑ x, v x = 1) : renyiOverlap α u v ≤ 1 := by
  calc renyiOverlap α u v ≤ ∑ x, (α * u x + (1 - α) * v x) :=
        Finset.sum_le_sum fun x _ => renyi_pointwise_le h0 h1 (hu x) (hv x)
    _ = 1 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu1, hv1]; ring

/-- **`(CDS.10)`.**  Strict Hölder/AM--GM equality: unit overlap characterizes identical
probability packets. -/
theorem renyiOverlap_eq_one_iff [Fintype X] {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {u v : X → ℝ}
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hu1 : ∑ x, u x = 1) (hv1 : ∑ x, v x = 1) :
    renyiOverlap α u v = 1 ↔ u = v := by
  constructor
  · intro h
    have hle : ∀ x, u x ^ α * v x ^ (1 - α) ≤ α * u x + (1 - α) * v x :=
      fun x => renyi_pointwise_le h0.le h1.le (hu x) (hv x)
    have hsum : ∑ x, (α * u x + (1 - α) * v x) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hu1, hv1]; ring
    have heq : ∀ x ∈ Finset.univ, u x ^ α * v x ^ (1 - α) = α * u x + (1 - α) * v x := by
      refine Finset.sum_eq_sum_iff_of_le (fun x _ => hle x) |>.mp ?_
      rw [hsum]; exact h
    funext x
    have hx := heq x (Finset.mem_univ x)
    exact (Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos h0 (by linarith) (hu x) (hv x)
      (by ring)).mp hx
  · rintro rfl
    have hone : α + (1 - α) = (1:ℝ) := by ring
    have : ∀ x, u x ^ α * u x ^ (1 - α) = u x := by
      intro x
      rw [← Real.rpow_add' (hu x) (by rw [hone]; norm_num), hone, Real.rpow_one]
    rw [renyiOverlap]
    simp_rw [this]
    exact hu1

/-- Hölder's inequality in Rényi form on a finite alphabet. -/
theorem sum_rpow_mul_rpow_le [Fintype X] {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {a b : X → ℝ}
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) :
    ∑ x, a x ^ α * b x ^ (1 - α) ≤ (∑ x, a x) ^ α * (∑ x, b x) ^ (1 - α) := by
  have hA0 : (0:ℝ) ≤ ∑ x, a x := Finset.sum_nonneg fun x _ => ha x
  have hB0 : (0:ℝ) ≤ ∑ x, b x := Finset.sum_nonneg fun x _ => hb x
  rcases eq_or_lt_of_le hA0 with hA | hA
  · have hzero : ∀ x, a x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => ha i).mp hA.symm x (Finset.mem_univ x)
    have hl : ∑ x, a x ^ α * b x ^ (1 - α) = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [hzero x, Real.zero_rpow (ne_of_gt h0), zero_mul]
    rw [hl, ← hA, Real.zero_rpow (ne_of_gt h0), zero_mul]
  rcases eq_or_lt_of_le hB0 with hB | hB
  · have hzero : ∀ x, b x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hb i).mp hB.symm x (Finset.mem_univ x)
    have hl : ∑ x, a x ^ α * b x ^ (1 - α) = 0 :=
      Finset.sum_eq_zero fun x _ => by
        rw [hzero x, Real.zero_rpow (by linarith : (1:ℝ) - α ≠ 0), mul_zero]
    rw [hl, ← hB, Real.zero_rpow (by linarith : (1:ℝ) - α ≠ 0), mul_zero]
  · have hden : (0:ℝ) < (∑ x, a x) ^ α * (∑ x, b x) ^ (1 - α) :=
      mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
    have hrw : ∀ x, (a x / (∑ y, a y)) ^ α * (b x / (∑ y, b y)) ^ (1 - α)
        = (a x ^ α * b x ^ (1 - α)) / ((∑ y, a y) ^ α * (∑ y, b y) ^ (1 - α)) := by
      intro x
      rw [Real.div_rpow (ha x) hA0, Real.div_rpow (hb x) hB0]
      field_simp
    have hstep : ∀ x, (a x / (∑ y, a y)) ^ α * (b x / (∑ y, b y)) ^ (1 - α)
        ≤ α * (a x / (∑ y, a y)) + (1 - α) * (b x / (∑ y, b y)) :=
      fun x => renyi_pointwise_le h0.le h1.le (div_nonneg (ha x) hA0) (div_nonneg (hb x) hB0)
    have hsum : ∑ x, (a x ^ α * b x ^ (1 - α))
        / ((∑ y, a y) ^ α * (∑ y, b y) ^ (1 - α)) ≤ 1 := by
      calc ∑ x, (a x ^ α * b x ^ (1 - α)) / ((∑ y, a y) ^ α * (∑ y, b y) ^ (1 - α))
          = ∑ x, (a x / (∑ y, a y)) ^ α * (b x / (∑ y, b y)) ^ (1 - α) := by
            exact Finset.sum_congr rfl fun x _ => (hrw x).symm
        _ ≤ ∑ x, (α * (a x / (∑ y, a y)) + (1 - α) * (b x / (∑ y, b y))) :=
            Finset.sum_le_sum fun x _ => hstep x
        _ = 1 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div,
              ← Finset.sum_div]
            field_simp
            ring
    rw [← Finset.sum_div] at hsum
    exact (div_le_one hden).mp hsum

/-- **Theorem 2.1 core, `(CDS.7)`.**  Rényi overlap is monotone upward under a finite Markov
kernel: no observation can lower it. -/
theorem renyiOverlap_markovDataProcessing [Fintype X] [Fintype Y] {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (K : FiniteMarkovKernel X Y) {u v : X → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    renyiOverlap α u v ≤ renyiOverlap α (K.toFinitePositiveKernel.applyReal u)
      (K.toFinitePositiveKernel.applyReal v) := by
  have hone : α + (1 - α) = (1:ℝ) := by ring
  have hsplit : ∀ (y : Y) (x : X),
      (K.weight y x * u x) ^ α * (K.weight y x * v x) ^ (1 - α)
        = K.weight y x * (u x ^ α * v x ^ (1 - α)) := by
    intro y x
    rw [Real.mul_rpow (K.nonneg y x) (hu x), Real.mul_rpow (K.nonneg y x) (hv x)]
    have : K.weight y x ^ α * K.weight y x ^ (1 - α) = K.weight y x := by
      rw [← Real.rpow_add' (K.nonneg y x) (by rw [hone]; norm_num), hone, Real.rpow_one]
    calc K.weight y x ^ α * u x ^ α * (K.weight y x ^ (1 - α) * v x ^ (1 - α))
        = (K.weight y x ^ α * K.weight y x ^ (1 - α)) * (u x ^ α * v x ^ (1 - α)) := by ring
      _ = K.weight y x * (u x ^ α * v x ^ (1 - α)) := by rw [this]
  have hy : ∀ y : Y, ∑ x, K.weight y x * (u x ^ α * v x ^ (1 - α))
      ≤ K.toFinitePositiveKernel.applyReal u y ^ α
        * K.toFinitePositiveKernel.applyReal v y ^ (1 - α) := by
    intro y
    have := sum_rpow_mul_rpow_le (X := X) h0 h1
      (a := fun x => K.weight y x * u x) (b := fun x => K.weight y x * v x)
      (fun x => mul_nonneg (K.nonneg y x) (hu x)) (fun x => mul_nonneg (K.nonneg y x) (hv x))
    simp only [hsplit y] at this
    exact this
  calc renyiOverlap α u v = ∑ x, (∑ y, K.weight y x) * (u x ^ α * v x ^ (1 - α)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [K.column_sum x, one_mul]
    _ = ∑ y, ∑ x, K.weight y x * (u x ^ α * v x ^ (1 - α)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]
    _ ≤ ∑ y, K.toFinitePositiveKernel.applyReal u y ^ α
          * K.toFinitePositiveKernel.applyReal v y ^ (1 - α) :=
        Finset.sum_le_sum fun y _ => hy y
    _ = renyiOverlap α (K.toFinitePositiveKernel.applyReal u)
          (K.toFinitePositiveKernel.applyReal v) := rfl

/-- Independent `d`-fold formation of a finite packet. -/
def tensorPower (d : ℕ) (p : X → ℝ) : (Fin d → X) → ℝ := fun f => ∏ i, p (f i)

theorem tensorPower_nonneg (d : ℕ) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (f : Fin d → X) :
    0 ≤ tensorPower d p f :=
  Finset.prod_nonneg fun i _ => hp (f i)

/-- Independent formation multiplies Rényi overlap. -/
theorem renyiOverlap_tensorPower [Fintype X] [DecidableEq X] (α : ℝ)
    (d : ℕ) {u v : X → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    renyiOverlap α (tensorPower d u) (tensorPower d v) = renyiOverlap α u v ^ d := by
  have hterm : ∀ f : Fin d → X,
      tensorPower d u f ^ α * tensorPower d v f ^ (1 - α)
        = ∏ i, u (f i) ^ α * v (f i) ^ (1 - α) := by
    intro f
    rw [tensorPower, tensorPower,
      ← Real.finsetProd_rpow _ _ (fun i _ => hu (f i)) α,
      ← Real.finsetProd_rpow _ _ (fun i _ => hv (f i)) (1 - α), ← Finset.prod_mul_distrib]
  rw [renyiOverlap]
  simp only [hterm]
  have hprod := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset X))
    (fun (_ : Fin d) (x : X) => u x ^ α * v x ^ (1 - α))
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  simp [renyiOverlap]

/-! ## Capital and formation arrays -/

theorem renyiCapital_antitone [Fintype X] [Fintype Y] {α : ℝ} {u v : X → ℝ} {u' v' : Y → ℝ}
    (h : renyiOverlap α u v ≤ renyiOverlap α u' v') :
    renyiCapital α u' v' ≤ renyiCapital α u v := by
  by_cases hs : 0 < renyiOverlap α u v
  · have hs' : 0 < renyiOverlap α u' v' := lt_of_lt_of_le hs h
    unfold renyiCapital
    rw [if_pos hs, if_pos hs']
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.log_le_log hs h])
  · unfold renyiCapital
    rw [if_neg hs]
    exact le_top

theorem renyiCapital_eq_zero_iff [Fintype X] {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {u v : X → ℝ}
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hu1 : ∑ x, u x = 1) (hv1 : ∑ x, v x = 1) :
    renyiCapital α u v = 0 ↔ u = v := by
  have hle := renyiOverlap_le_one h0.le h1.le hu hv hu1 hv1
  constructor
  · intro h
    unfold renyiCapital at h
    split_ifs at h with hpos
    · have : -Real.log (renyiOverlap α u v) ≤ 0 := by
        by_contra hcon
        push Not at hcon
        exact absurd h (by simp [ENNReal.ofReal_eq_zero]; linarith)
      have hlog : 0 ≤ Real.log (renyiOverlap α u v) := by linarith
      have : 1 ≤ renyiOverlap α u v := by
        by_contra hcon
        push Not at hcon
        exact absurd hlog (not_le.mpr (Real.log_neg hpos hcon))
      exact (renyiOverlap_eq_one_iff h0 h1 hu hv hu1 hv1).mp (le_antisymm hle this)
    · exact absurd h (by simp)
  · rintro rfl
    have h1' : renyiOverlap α u u = 1 := (renyiOverlap_eq_one_iff h0 h1 hu hu hu1 hu1).mpr rfl
    unfold renyiCapital
    rw [h1']
    simp

/-- Independent formation multiplies capital by the formed depth. -/
theorem renyiCapital_tensorPower [Fintype X] [DecidableEq X] {α : ℝ} (d : ℕ)
    {u v : X → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    renyiCapital α (tensorPower d u) (tensorPower d v) = d * renyiCapital α u v := by
  have hpow := renyiOverlap_tensorPower α d hu hv
  have hnn : 0 ≤ renyiOverlap α u v := renyiOverlap_nonneg hu hv
  rcases eq_or_lt_of_le hnn with hzero | hpos
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · have hone : renyiOverlap α (tensorPower 0 u) (tensorPower 0 v) = 1 := by
        rw [hpow, pow_zero]
      unfold renyiCapital
      rw [hone]
      simp
    · have hz : renyiOverlap α (tensorPower d u) (tensorPower d v) = 0 := by
        rw [hpow, ← hzero, zero_pow (by omega)]
      have hcu : renyiCapital α u v = ⊤ := by
        unfold renyiCapital
        rw [if_neg (by rw [← hzero]; exact lt_irrefl 0)]
      have hcp : renyiCapital α (tensorPower d u) (tensorPower d v) = ⊤ := by
        unfold renyiCapital
        rw [if_neg (by rw [hz]; exact lt_irrefl 0)]
      rw [hcu, hcp, ENNReal.mul_top (by exact_mod_cast hd.ne')]
  · unfold renyiCapital
    rw [hpow, if_pos (pow_pos hpos d), if_pos hpos, Real.log_pow]
    rw [← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    congr 1
    ring

/-- Total mass of an independent `d`-fold formation. -/
theorem sum_tensorPower [Fintype X] [DecidableEq X] (d : ℕ) (p : X → ℝ) :
    ∑ f : Fin d → X, tensorPower d p f = (∑ x, p x) ^ d := by
  have hprod := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset X))
    (fun (_ : Fin d) (x : X) => p x)
  rw [Fintype.piFinset_univ] at hprod
  simpa [tensorPower] using hprod.symm

/-- `(CDS.1)`, `(CDS.2)`  A finite binary experiment. -/
structure FiniteExperiment (X : Type*) [Fintype X] where
  law₀ : X → ℝ
  law₁ : X → ℝ
  nonneg₀ : ∀ x, 0 ≤ law₀ x
  nonneg₁ : ∀ x, 0 ≤ law₁ x
  sum₀ : ∑ x, law₀ x = 1
  sum₁ : ∑ x, law₁ x = 1

namespace FiniteExperiment

/-- `(CDS.5)`  Rényi capital of a finite binary experiment. -/
def capital [Fintype X] (α : ℝ) (E : FiniteExperiment X) : ℝ≥0∞ :=
  renyiCapital α E.law₀ E.law₁

/-- Independent `d`-fold formation of an experiment. -/
def tensorPow [Fintype X] [DecidableEq X] (d : ℕ) (E : FiniteExperiment X) :
    FiniteExperiment (Fin d → X) where
  law₀ := tensorPower d E.law₀
  law₁ := tensorPower d E.law₁
  nonneg₀ := tensorPower_nonneg d E.nonneg₀
  nonneg₁ := tensorPower_nonneg d E.nonneg₁
  sum₀ := by rw [sum_tensorPower, E.sum₀, one_pow]
  sum₁ := by rw [sum_tensorPower, E.sum₁, one_pow]

/-- **Corollary 5.2, `(CDS.23)`.**  Independent formation multiplies capital exactly. -/
theorem capital_tensorPow [Fintype X] [DecidableEq X] {α : ℝ} (d : ℕ) (E : FiniteExperiment X) :
    (E.tensorPow d).capital α = d * E.capital α :=
  renyiCapital_tensorPower d E.nonneg₀ E.nonneg₁

/-- `(CDS.6)`  Source capital density: capital per formed copy. -/
def capitalDensity [Fintype X] (α : ℝ) (E : FiniteExperiment X) (d : ℕ) : ℝ≥0∞ :=
  E.capital α / d

end FiniteExperiment

/-- `(CDS.3)`, `(CDS.4)`  An exact formation array: one Markov kernel carrying the source
experiment onto `d` independent copies of the target experiment. -/
structure ExactFormation {S X : Type*} [Fintype S] [Fintype X] [DecidableEq X]
    (E : FiniteExperiment S) (F : FiniteExperiment X) (d : ℕ) where
  kernel : FiniteMarkovKernel S (Fin d → X)
  forms_zero : kernel.toFinitePositiveKernel.applyReal E.law₀ = (F.tensorPow d).law₀
  forms_one : kernel.toFinitePositiveKernel.applyReal E.law₁ = (F.tensorPow d).law₁

/-- **Theorem 2.1, `(CDS.7)`.**  Every exact formation array pays the whole formed target capital
out of source capital. -/
theorem ExactFormation.capital_le {S X : Type*} [Fintype S] [Fintype X] [DecidableEq X] {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) {E : FiniteExperiment S} {F : FiniteExperiment X} {d : ℕ}
    (A : ExactFormation E F d) :
    (d : ℝ≥0∞) * F.capital α ≤ E.capital α := by
  have hdp := renyiOverlap_markovDataProcessing h0 h1 A.kernel E.nonneg₀ E.nonneg₁
  rw [A.forms_zero, A.forms_one] at hdp
  have hcap := renyiCapital_antitone hdp
  rw [← FiniteExperiment.capital, ← FiniteExperiment.capital,
    FiniteExperiment.capital_tensorPow] at hcap
  exact hcap

/-- **Theorem 2.1, `(CDS.7)` density form.**  Target capital is bounded by source capital
density. -/
theorem ExactFormation.capital_le_density {S X : Type*} [Fintype S] [Fintype X] [DecidableEq X]
    {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {E : FiniteExperiment S} {F : FiniteExperiment X} {d : ℕ}
    (hd : 0 < d) (A : ExactFormation E F d) :
    F.capital α ≤ E.capitalDensity α d := by
  rw [FiniteExperiment.capitalDensity, ENNReal.le_div_iff_mul_le
    (Or.inl (by exact_mod_cast hd.ne')) (Or.inl (by simp))]
  rw [mul_comm]
  exact A.capital_le h0 h1

/-- **Theorem 2.2, `(CDS.9)`.**  Vanishing capital density forces vanishing target capital. -/
theorem tendsto_capital_of_tendsto_density {C ρ : ℕ → ℝ≥0∞} (h : ∀ n, C n ≤ ρ n)
    (hρ : Filter.Tendsto ρ Filter.atTop (nhds 0)) :
    Filter.Tendsto C Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hρ (fun _ => bot_le) h

/-- **Theorem 2.2, `(CDS.10)`.**  A target experiment of zero capital is neutral. -/
theorem FiniteExperiment.capital_eq_zero_iff [Fintype X] {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (F : FiniteExperiment X) : F.capital α = 0 ↔ F.law₀ = F.law₁ :=
  renyiCapital_eq_zero_iff h0 h1 F.nonneg₀ F.nonneg₁ F.sum₀ F.sum₁

/-- **`(CDS.12)`.**  A source-normal coercivity law converts a capital-density bound into a
quantitative displacement bound. -/
theorem coercivity_displacement_bound {c q δ ρ : ℝ} (hc : 0 < c) (hq : 0 < q) (hδ : 0 ≤ δ)
    (hcoer : c * δ ^ q ≤ ρ) : δ ≤ (ρ / c) ^ (1 / q) := by
  have hρ : 0 ≤ ρ := le_trans (by positivity) hcoer
  have hle : δ ^ q ≤ ρ / c := by
    rw [le_div_iff₀ hc, mul_comm]
    exact hcoer
  have hid : (δ ^ q) ^ (1 / q) = δ := by
    rw [← Real.rpow_mul hδ, mul_one_div, div_self hq.ne', Real.rpow_one]
  calc δ = (δ ^ q) ^ (1 / q) := hid.symm
    _ ≤ (ρ / c) ^ (1 / q) := Real.rpow_le_rpow (by positivity) hle (by positivity)

/-- **Theorem 5.1, `(CDS.22)`.**  Capital is invariant under Blackwell equivalence. -/
theorem capital_eq_of_blackwellEquivalent {S T : Type*} [Fintype S] [Fintype T] {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) {E : FiniteExperiment S} {M : FiniteExperiment T}
    (K : FiniteMarkovKernel S T) (L : FiniteMarkovKernel T S)
    (hK₀ : K.toFinitePositiveKernel.applyReal E.law₀ = M.law₀)
    (hK₁ : K.toFinitePositiveKernel.applyReal E.law₁ = M.law₁)
    (hL₀ : L.toFinitePositiveKernel.applyReal M.law₀ = E.law₀)
    (hL₁ : L.toFinitePositiveKernel.applyReal M.law₁ = E.law₁) :
    E.capital α = M.capital α := by
  have h₁ := renyiOverlap_markovDataProcessing h0 h1 K E.nonneg₀ E.nonneg₁
  have h₂ := renyiOverlap_markovDataProcessing h0 h1 L M.nonneg₀ M.nonneg₁
  rw [hK₀, hK₁] at h₁
  rw [hL₀, hL₁] at h₂
  have : renyiOverlap α E.law₀ E.law₁ = renyiOverlap α M.law₀ M.law₁ := le_antisymm h₁ h₂
  unfold FiniteExperiment.capital renyiCapital
  rw [this]

end

end GaloisForLFunctions.HTGeometry
