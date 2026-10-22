import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The paired source is uniformly `ℓ²`-bounded

Each coordinate of the literal paired source is a weighted centred difference of the completed
eigenmode,

`F_i(L) = w_i [u(x_i + o_i e^{-L}) − u(x_i)]`,

so it is bounded by `2‖u‖_∞ w_i` uniformly in the scale — no continuity, no modulus, only
boundedness of `u`.  Summing the squares gives the uniform `ℓ²` bound

`‖F(L)‖_{ℓ²} ≤ 2‖u‖_∞ ‖w‖_{ℓ²}`,

with the constant independent of `L`.  The statement is indexed by an arbitrary type, so it applies
verbatim to the two-coset index set `{+,−} × G × {±1}`: there `w` is the orbit weight repeated over
the four sign combinations, and `‖w‖_{ℓ²}` is its norm over the whole index set.
-/

open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {ι : Type*}

/-- The paired-source profile: a weighted centred difference of the eigenmode. -/
def pairedSourceEntry (w x o : ι → ℝ) (u : ℝ → ℝ) (i : ι) (L : ℝ) : ℝ :=
  w i * (u (x i + o i * Real.exp (-L)) - u (x i))

/-- **Every entry is bounded by twice the sup norm times the weight, uniformly in the scale.** -/
theorem abs_pairedSourceEntry_le {w x o : ι → ℝ} {u : ℝ → ℝ} {M : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ y, |u y| ≤ M) (i : ι) (L : ℝ) :
    |pairedSourceEntry w x o u i L| ≤ 2 * M * w i := by
  have hdiff : |u (x i + o i * Real.exp (-L)) - u (x i)| ≤ 2 * M := by
    have h1 := hu (x i + o i * Real.exp (-L))
    have h2 := hu (x i)
    calc |u (x i + o i * Real.exp (-L)) - u (x i)|
        ≤ |u (x i + o i * Real.exp (-L))| + |u (x i)| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  rw [pairedSourceEntry, abs_mul]
  calc |w i| * |u (x i + o i * Real.exp (-L)) - u (x i)|
      = w i * |u (x i + o i * Real.exp (-L)) - u (x i)| := by
        rw [abs_of_nonneg (hw i)]
    _ ≤ w i * (2 * M) := mul_le_mul_of_nonneg_left hdiff (hw i)
    _ = 2 * M * w i := by ring

/-- The squared entry is dominated by the squared weight. -/
theorem sq_pairedSourceEntry_le {w x o : ι → ℝ} {u : ℝ → ℝ} {M : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ y, |u y| ≤ M) (i : ι) (L : ℝ) :
    (pairedSourceEntry w x o u i L) ^ 2 ≤ (2 * M) ^ 2 * (w i) ^ 2 := by
  have habs := abs_pairedSourceEntry_le (x := x) (o := o) hw hu i L
  have hnn : (0 : ℝ) ≤ 2 * M * w i := le_trans (abs_nonneg _) habs
  have hsq : (pairedSourceEntry w x o u i L) ^ 2 ≤ (2 * M * w i) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  refine hsq.trans (le_of_eq ?_)
  ring

/-- **`(3)` in extended form: the uniform `ℓ²` bound.**  No summability hypothesis is needed. -/
theorem tsum_sq_pairedSourceEntry_le {w x o : ι → ℝ} {u : ℝ → ℝ} {M : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ y, |u y| ≤ M) (L : ℝ) :
    (∑' i : ι, ENNReal.ofReal ((pairedSourceEntry w x o u i L) ^ 2))
      ≤ ENNReal.ofReal ((2 * M) ^ 2) * ∑' i : ι, ENNReal.ofReal ((w i) ^ 2) := by
  have hterm : ∀ i : ι, ENNReal.ofReal ((pairedSourceEntry w x o u i L) ^ 2)
      ≤ ENNReal.ofReal ((2 * M) ^ 2) * ENNReal.ofReal ((w i) ^ 2) := by
    intro i
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (sq_pairedSourceEntry_le hw hu i L)
  calc (∑' i : ι, ENNReal.ofReal ((pairedSourceEntry w x o u i L) ^ 2))
      ≤ ∑' i : ι, ENNReal.ofReal ((2 * M) ^ 2) * ENNReal.ofReal ((w i) ^ 2) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal ((2 * M) ^ 2) * ∑' i : ι, ENNReal.ofReal ((w i) ^ 2) := by
        rw [ENNReal.tsum_mul_left]

/-- **`(3)` in real form.**  A square-summable weight makes the paired source square summable, with
the uniform bound `‖F(L)‖²_{ℓ²} ≤ (2‖u‖_∞)² ‖w‖²_{ℓ²}`. -/
theorem summable_sq_pairedSourceEntry {w x o : ι → ℝ} {u : ℝ → ℝ} {M : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ y, |u y| ≤ M) (hsum : Summable fun i => (w i) ^ 2) (L : ℝ) :
    Summable (fun i => (pairedSourceEntry w x o u i L) ^ 2) ∧
      (∑' i : ι, (pairedSourceEntry w x o u i L) ^ 2)
        ≤ (2 * M) ^ 2 * ∑' i : ι, (w i) ^ 2 := by
  have hmaj : Summable fun i => (2 * M) ^ 2 * (w i) ^ 2 := hsum.mul_left _
  have hsummable : Summable (fun i => (pairedSourceEntry w x o u i L) ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => sq_pairedSourceEntry_le hw hu i L)
      hmaj
  refine ⟨hsummable, ?_⟩
  calc (∑' i : ι, (pairedSourceEntry w x o u i L) ^ 2)
      ≤ ∑' i : ι, (2 * M) ^ 2 * (w i) ^ 2 :=
        hsummable.tsum_mono hmaj fun i => sq_pairedSourceEntry_le hw hu i L
    _ = (2 * M) ^ 2 * ∑' i : ι, (w i) ^ 2 := tsum_mul_left

end GaloisForLFunctions.RHTower
