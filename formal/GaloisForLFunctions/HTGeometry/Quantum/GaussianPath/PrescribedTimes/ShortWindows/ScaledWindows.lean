import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.IsolatedDilations
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin

/-! # Separating observation windows by small changes of the coupling radius -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
noncomputable section

/-- The i-th dilation moves the prescribed delay L by exactly i times g. -/
def factor {m : ℕ} (g L : ℝ) (i : Fin m) : ℝ := 1+(i.val:ℝ)*g/L

theorem factor_bounds {m : ℕ} {g L : ℝ} (hg : 0 ≤ g) (hL : 0 < L) (hm : (m:ℝ)*g ≤ L) (i : Fin m) :
    factor g L i∈Icc (1:ℝ) 2 := by
  have hi : (i.val:ℝ) ≤ m := by exact_mod_cast i.isLt.le
  have hh := (div_le_one hL).mpr ((mul_le_mul_of_nonneg_right hi hg).trans hm)
  exact ⟨le_add_of_nonneg_right (div_nonneg (mul_nonneg (Nat.cast_nonneg i.val) hg) hL.le),by
    dsimp only [factor]; linarith only [hh]⟩

private theorem grid_gap {m : ℕ} {g L : ℝ} (hg : 0 ≤ g) (hL : 0 < L) (hm : (m:ℝ)*g ≤ L)
    (i j : Fin m) (hne : j≠i) :
    let p := factor g L j/factor g L i
    g/2 ≤ |p*L-L| ∧ |p*L-L| ≤ (m:ℝ)*g := by
  intro p
  have hi := factor_bounds hg hL hm i
  have hi0 := zero_lt_one.trans_le hi.1
  have hji : j.val ≠ i.val := fun he => hne (Fin.ext he)
  have hbase : 1 ≤ |(j.val:ℝ)-(i.val:ℝ)| := by
    rcases lt_or_gt_of_ne hji with h | h
    · have h' : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith only [h'])]
      linarith only [h']
    · have h' : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith only [h'])]
      linarith only [h']
  have htop : |(j.val:ℝ)-(i.val:ℝ)| ≤ m := by
    have hi' : (i.val:ℝ) ≤ m := by exact_mod_cast i.isLt.le
    have hj' : (j.val:ℝ) ≤ m := by exact_mod_cast j.isLt.le
    rw [abs_le]
    constructor <;> linarith only [hi',hj',Nat.cast_nonneg (α:=ℝ) j.val,Nat.cast_nonneg (α:=ℝ) i.val]
  have he : p*L-L=((j.val:ℝ)-i.val)*g/factor g L i := by
    dsimp only [p]
    field_simp [hi0.ne']
    dsimp only [factor]
    field_simp [hL.ne']
    ring
  rw [he,abs_div,abs_mul,abs_of_nonneg hg,abs_of_pos hi0]
  constructor
  · apply (le_div_iff₀ hi0).mpr
    calc
      _ ≤ g/2*2 := mul_le_mul_of_nonneg_left hi.2 (by positivity)
      _ = 1*g := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbase hg
  · exact (div_le_self (mul_nonneg (abs_nonneg _) hg) hi.1).trans (mul_le_mul_of_nonneg_right htop hg)

/-- From the same crossing origin, a hit in two different rescaled
windows forces an affordable lag between g/2−2w and mg+2w. -/
theorem window_gap {m : ℕ} {g L w σ : ℝ} (hg : 0 ≤ g) (hL : 0 < L) (hm : (m:ℝ)*g ≤ L)
    (hw : 0 ≤ w) (i j : Fin m) (hne : j≠i) {t u : ℝ}
    (ht : t∈Icc (σ+L) (σ+L+w))
    (hu : let p := factor g L j/factor g L i
          u∈Icc (σ+p*L) (σ+p*L+p*w)) :
    g/2-2*w ≤ |u-t| ∧ |u-t| ≤ (m:ℝ)*g+2*w := by
  let p := factor g L j/factor g L i
  change u∈Icc (σ+p*L) (σ+p*L+p*w) at hu
  have hi := factor_bounds hg hL hm i
  have hj := factor_bounds hg hL hm j
  have hp : p ≤ 2 := (div_le_self (zero_le_one.trans hj.1) hi.1).trans hj.2
  have hnoise : |(u-t)-(p*L-L)| ≤ 2*w := by
    rw [abs_le]
    constructor <;> linarith only [hu.1,hu.2,ht.1,ht.2,mul_le_mul_of_nonneg_right hp hw,hw]
  obtain ⟨hl,hh⟩ := grid_gap hg hL hm i j hne
  change g/2 ≤ |p*L-L| at hl
  change |p*L-L| ≤ (m:ℝ)*g at hh
  have h₁ := abs_add_le ((u-t)-(p*L-L)) (p*L-L)
  have h₂ := abs_add_le ((p*L-L)-(u-t)) (u-t)
  rw [sub_add_cancel] at h₁
  rw [sub_add_cancel,abs_sub_comm (p*L-L) (u-t)] at h₂
  constructor <;> linarith only [hl,hh,h₁,h₂,hnoise]

/-- A physical return window at elapsed delay L following the first crossing. -/
def hitWindow (n P s : ℕ) (L w : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | let σ := crossingOrigin n P (9/80) x
       ∃ t∈Icc (σ+L) (σ+L+w), pathGateDistance n s x t ≤ 1/10}

theorem measurable_hitWindow (n P s : ℕ) (L w : ℝ) : MeasurableSet (hitWindow n P s L w) :=
  measurable_shifted_window _ _ _ (measurable_crossingOrigin _ _ _) _ _

/-- A forbidden band of lags makes any hit isolated in the grid. -/
theorem isolated_of_gap {m n P s : ℕ} {g L w : ℝ} (hg : 0 ≤ g) (hL : 0 < L) (hm : (m:ℝ)*g ≤ L)
    (hw : 0 ≤ w) (x : PrefixIndex n → ℝ) (hx : x∈hitWindow n P s L w)
    (hgap : ∀ t u : ℝ, pathGateDistance n s x t ≤ 1/10 → pathGateDistance n s x u ≤ 1/10 →
      g/2-2*w ≤ |u-t| → |u-t| ≤ (m:ℝ)*g+2*w → False) :
    x∈isolated (factor (m:=m) g L) (hitWindow n P s L w) := by
  apply mem_isolated hx
  obtain ⟨t,ht,hcheap⟩ := hx
  intro i j hne hj
  have hp : 0 < factor g L j/factor g L i := div_pos
    (zero_lt_one.trans_le (factor_bounds hg hL hm j).1) (zero_lt_one.trans_le (factor_bounds hg hL hm i).1)
  obtain ⟨u,hu,hcheap'⟩ := (crossing_window_dilate n P s (9/80) (1/10) L w hp x).mp hj
  obtain ⟨hl,hh⟩ := window_gap hg hL hm hw i j hne ht hu
  exact hgap t u hcheap hcheap' hl hh

#print axioms isolated_of_gap
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
