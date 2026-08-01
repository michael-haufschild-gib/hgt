import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-!
# The solution set of a relation is a Lipschitz graph where a partial derivative dominates

Let `P` be holomorphic on a convex region and suppose its derivative stays within `C` of a fixed
linear functional `L` there.  The mean value inequality against `L` says the increment of `P` between
two points of the region differs from `L` applied to the increment by at most `C` times its size.  On
solutions of `P = 0` the increment of `P` vanishes, so `L` applied to the increment is small; and
since `L` decomposes into partial derivatives, the coordinate whose partial dominates `C` is
controlled by the others.

That is the quantitative implicit function theorem the finite-phase law needs: near a jet where the
separant does not vanish, the top derivative of a solution is a Lipschitz function of the lower ones,
and in particular it is determined by them.
-/

open Filter Topology Metric Set Finset

namespace GaloisForLFunctions

variable {m : ℕ}

/-- The partial derivatives of a continuous linear functional on a finite product. -/
noncomputable def partialCoeff (L : ((Fin m) → ℂ) →L[ℂ] ℂ) (k : Fin m) : ℂ :=
  L (Pi.single k 1)

theorem apply_eq_sum_partial (L : ((Fin m) → ℂ) →L[ℂ] ℂ) (Δ : Fin m → ℂ) :
    L Δ = ∑ k, Δ k * partialCoeff L k := by
  have hdecomp : Δ = ∑ k, Pi.single k (Δ k) := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [hdecomp, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsingle : (Pi.single k (Δ k) : Fin m → ℂ) = (Δ k) • Pi.single k 1 := by
    funext j
    by_cases h : j = k <;> simp [h]
  rw [hsingle, map_smul, partialCoeff]
  simp [smul_eq_mul]

/-- **Implicit Lipschitz estimate.**  On a convex region where the derivative of `P` stays close to a
fixed linear functional whose `j₀`-th partial dominates the deviation, the `j₀`-th coordinate of a
solution of `P = 0` is a Lipschitz function of the remaining coordinates. -/
theorem implicit_lipschitz_estimate {P : (Fin m → ℂ) → ℂ}
    {P' : (Fin m → ℂ) → ((Fin m → ℂ) →L[ℂ] ℂ)} {S : Set (Fin m → ℂ)} (hS : Convex ℝ S)
    (hP : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
    {L : (Fin m → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y ∈ S, ‖P' y - L‖ ≤ C) (j₀ : Fin m)
    {y z : Fin m → ℂ} (hy : y ∈ S) (hz : z ∈ S) (hPy : P y = 0) (hPz : P z = 0) :
    (‖partialCoeff L j₀‖ - C) * ‖y j₀ - z j₀‖
      ≤ (C + ∑ k ∈ Finset.univ.erase j₀, ‖partialCoeff L k‖)
        * ∑ k ∈ Finset.univ.erase j₀, ‖y k - z k‖ := by
  classical
  set Δ : Fin m → ℂ := y - z with hΔ
  set T : ℝ := ∑ k ∈ Finset.univ.erase j₀, ‖y k - z k‖ with hT
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg fun k _ => norm_nonneg _
  -- mean value inequality against the fixed functional
  have hmvt : ‖P y - P z - (L.restrictScalars ℝ) (y - z)‖ ≤ C * ‖y - z‖ := by
    refine hS.norm_image_sub_le_of_norm_hasFDerivWithin_le' hP ?_ hz hy
    intro x hx
    have : (P' x).restrictScalars ℝ - L.restrictScalars ℝ = (P' x - L).restrictScalars ℝ := rfl
    rw [this, ContinuousLinearMap.norm_restrictScalars]
    exact hbound x hx
  rw [hPy, hPz] at hmvt
  have hLΔ : ‖L (y - z)‖ ≤ C * ‖y - z‖ := by
    have hrs : (L.restrictScalars ℝ) (y - z) = L (y - z) := rfl
    rw [hrs] at hmvt
    have hzero : (0 : ℂ) - 0 - L (y - z) = -(L (y - z)) := by ring
    rw [hzero, norm_neg] at hmvt
    exact hmvt
  -- decompose the functional
  have hsum : L (y - z) = ∑ k, (y k - z k) * partialCoeff L k := by
    have := apply_eq_sum_partial L (y - z)
    simpa using this
  have hsplit : (y j₀ - z j₀) * partialCoeff L j₀
      = L (y - z) - ∑ k ∈ Finset.univ.erase j₀, (y k - z k) * partialCoeff L k := by
    rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]
    ring
  -- bound the two pieces
  have hnormΔ : ‖y - z‖ ≤ ‖y j₀ - z j₀‖ + T := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    by_cases hk : k = j₀
    · subst hk
      have : (0:ℝ) ≤ T := hTnonneg
      have hval : ‖(y - z) k‖ = ‖y k - z k‖ := rfl
      rw [hval]
      linarith
    · have hmem : k ∈ Finset.univ.erase j₀ := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩
      have hle : ‖y k - z k‖ ≤ T :=
        Finset.single_le_sum (f := fun k => ‖y k - z k‖) (fun i _ => norm_nonneg _) hmem
      have hval : ‖(y - z) k‖ = ‖y k - z k‖ := rfl
      rw [hval]
      have : (0:ℝ) ≤ ‖y j₀ - z j₀‖ := norm_nonneg _
      linarith
  have hrest : ‖∑ k ∈ Finset.univ.erase j₀, (y k - z k) * partialCoeff L k‖
      ≤ (∑ k ∈ Finset.univ.erase j₀, ‖partialCoeff L k‖) * T := by
    calc ‖∑ k ∈ Finset.univ.erase j₀, (y k - z k) * partialCoeff L k‖
        ≤ ∑ k ∈ Finset.univ.erase j₀, ‖(y k - z k) * partialCoeff L k‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.univ.erase j₀, ‖y k - z k‖ * ‖partialCoeff L k‖ := by
          exact Finset.sum_congr rfl fun k _ => norm_mul _ _
      _ ≤ ∑ k ∈ Finset.univ.erase j₀, T * ‖partialCoeff L k‖ := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hle : ‖y k - z k‖ ≤ T :=
            Finset.single_le_sum (f := fun k => ‖y k - z k‖) (fun i _ => norm_nonneg _) hk
          exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = (∑ k ∈ Finset.univ.erase j₀, ‖partialCoeff L k‖) * T := by
          rw [← Finset.mul_sum, mul_comm]
  have hmain : ‖y j₀ - z j₀‖ * ‖partialCoeff L j₀‖
      ≤ C * (‖y j₀ - z j₀‖ + T) + (∑ k ∈ Finset.univ.erase j₀, ‖partialCoeff L k‖) * T := by
    have h1 : ‖(y j₀ - z j₀) * partialCoeff L j₀‖ ≤ ‖L (y - z)‖
        + ‖∑ k ∈ Finset.univ.erase j₀, (y k - z k) * partialCoeff L k‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    rw [norm_mul] at h1
    have h2 : ‖L (y - z)‖ ≤ C * (‖y j₀ - z j₀‖ + T) :=
      le_trans hLΔ (mul_le_mul_of_nonneg_left hnormΔ hC)
    linarith [hrest]
  nlinarith [hmain, norm_nonneg (y j₀ - z j₀), hTnonneg]

/-- **Uniqueness of the distinguished coordinate.**  Two solutions in the region agreeing in all
other coordinates agree in the distinguished one. -/
theorem eq_of_erase_eq {P : (Fin m → ℂ) → ℂ}
    {P' : (Fin m → ℂ) → ((Fin m → ℂ) →L[ℂ] ℂ)} {S : Set (Fin m → ℂ)} (hS : Convex ℝ S)
    (hP : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
    {L : (Fin m → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ y ∈ S, ‖P' y - L‖ ≤ C) (j₀ : Fin m) (hdom : C < ‖partialCoeff L j₀‖)
    {y z : Fin m → ℂ} (hy : y ∈ S) (hz : z ∈ S) (hPy : P y = 0) (hPz : P z = 0)
    (hother : ∀ k, k ≠ j₀ → y k = z k) : y j₀ = z j₀ := by
  classical
  have hest := implicit_lipschitz_estimate hS hP hC hbound j₀ hy hz hPy hPz
  have hT : (∑ k ∈ Finset.univ.erase j₀, ‖y k - z k‖) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hne : k ≠ j₀ := (Finset.mem_erase.mp hk).1
    rw [hother k hne, sub_self, norm_zero]
  rw [hT, mul_zero] at hest
  have hpos : 0 < ‖partialCoeff L j₀‖ - C := by linarith
  have hnorm : ‖y j₀ - z j₀‖ ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have : ‖y j₀ - z j₀‖ = 0 := le_antisymm hnorm (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

section Extension

variable {n : ℕ}

/-- A complex-valued Lipschitz function on a set extends to a Lipschitz function on the whole
space, at the cost of a factor two. -/
theorem LipschitzOnWith.extend_complex {α : Type*} [PseudoMetricSpace α] {f : α → ℂ} {s : Set α}
    {K : NNReal} (hf : LipschitzOnWith K f s) :
    ∃ g : α → ℂ, LipschitzWith (2 * K) g ∧ Set.EqOn f g s := by
  have hre : LipschitzOnWith K (fun a => (f a).re) s := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h := hf.dist_le_mul x hx y hy
    calc dist (f x).re (f y).re = |(f x).re - (f y).re| := Real.dist_eq _ _
      _ = |(f x - f y).re| := by rw [Complex.sub_re]
      _ ≤ ‖f x - f y‖ := Complex.abs_re_le_norm _
      _ = dist (f x) (f y) := (dist_eq_norm _ _).symm
      _ ≤ (K : ℝ) * dist x y := h
  have him : LipschitzOnWith K (fun a => (f a).im) s := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h := hf.dist_le_mul x hx y hy
    calc dist (f x).im (f y).im = |(f x).im - (f y).im| := Real.dist_eq _ _
      _ = |(f x - f y).im| := by rw [Complex.sub_im]
      _ ≤ ‖f x - f y‖ := Complex.abs_im_le_norm _
      _ = dist (f x) (f y) := (dist_eq_norm _ _).symm
      _ ≤ (K : ℝ) * dist x y := h
  obtain ⟨u, hu, hueq⟩ := hre.extend_real
  obtain ⟨v, hv, hveq⟩ := him.extend_real
  refine ⟨fun a => Complex.mk (u a) (v a), ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hu' : |u x - u y| ≤ (K : ℝ) * dist x y := by
      have := hu.dist_le_mul x y
      rwa [Real.dist_eq] at this
    have hv' : |v x - v y| ≤ (K : ℝ) * dist x y := by
      have := hv.dist_le_mul x y
      rwa [Real.dist_eq] at this
    have hsub : (Complex.mk (u x) (v x) - Complex.mk (u y) (v y)).re = u x - u y := rfl
    have hsub' : (Complex.mk (u x) (v x) - Complex.mk (u y) (v y)).im = v x - v y := rfl
    rw [dist_eq_norm]
    calc ‖Complex.mk (u x) (v x) - Complex.mk (u y) (v y)‖
        ≤ |(Complex.mk (u x) (v x) - Complex.mk (u y) (v y)).re|
          + |(Complex.mk (u x) (v x) - Complex.mk (u y) (v y)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |u x - u y| + |v x - v y| := by rw [hsub, hsub']
      _ ≤ (K : ℝ) * dist x y + (K : ℝ) * dist x y := add_le_add hu' hv'
      _ = ((2 * K : NNReal) : ℝ) * dist x y := by push_cast; ring
  · intro a ha
    refine Complex.ext ?_ ?_
    · exact hueq ha
    · exact hveq ha

/-- **A Lipschitz graph over the lower coordinates is cut out by a Lipschitz function.** -/
theorem exists_lipschitz_of_graph {S : Set (Fin (n + 1) → ℂ)} {P : (Fin (n + 1) → ℂ) → ℂ}
    {M : NNReal}
    (hgraph : ∀ y ∈ S, P y = 0 → ∀ z ∈ S, P z = 0 →
      dist (y (Fin.last n)) (z (Fin.last n))
        ≤ (M : ℝ) * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc)) :
    ∃ Φ : (Fin n → ℂ) → ℂ, LipschitzWith (2 * M) Φ ∧
      ∀ y ∈ S, P y = 0 → y (Fin.last n) = Φ (fun k : Fin n => y k.castSucc) := by
  classical
  set proj : (Fin (n + 1) → ℂ) → (Fin n → ℂ) := fun y k => y k.castSucc with hproj
  set D : Set (Fin n → ℂ) := proj '' {y | y ∈ S ∧ P y = 0} with hD
  set Φ₀ : (Fin n → ℂ) → ℂ := fun w => if h : w ∈ D then (h.choose) (Fin.last n) else 0 with hΦ₀
  have hval : ∀ (w : Fin n → ℂ) (h : w ∈ D), Φ₀ w = (h.choose) (Fin.last n) := by
    intro w h
    rw [hΦ₀]
    simp only [dif_pos h]
  have hspec : ∀ (w : Fin n → ℂ) (h : w ∈ D),
      (h.choose ∈ S ∧ P h.choose = 0) ∧ proj h.choose = w := fun w h => h.choose_spec
  -- the partial function is Lipschitz on its domain
  have hlip : LipschitzOnWith M Φ₀ D := by
    refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_
    obtain ⟨⟨hyS, hyP⟩, hyproj⟩ := hspec w hw
    obtain ⟨⟨hzS, hzP⟩, hzproj⟩ := hspec w' hw'
    rw [hval w hw, hval w' hw']
    have h := hgraph _ hyS hyP _ hzS hzP
    rw [show (fun k : Fin n => (hw.choose) k.castSucc) = w from hyproj,
      show (fun k : Fin n => (hw'.choose) k.castSucc) = w' from hzproj] at h
    exact h
  -- the partial function computes the top coordinate of any solution
  have hsol : ∀ y ∈ S, P y = 0 → y (Fin.last n) = Φ₀ (proj y) := by
    intro y hyS hyP
    have hmem : proj y ∈ D := ⟨y, ⟨hyS, hyP⟩, rfl⟩
    obtain ⟨⟨hzS, hzP⟩, hzproj⟩ := hspec (proj y) hmem
    rw [hval (proj y) hmem]
    have h := hgraph _ hyS hyP _ hzS hzP
    rw [show (fun k : Fin n => (hmem.choose) k.castSucc) = proj y from hzproj] at h
    have hdz : dist (proj y) (proj y) = 0 := dist_self _
    rw [show (fun k : Fin n => y k.castSucc) = proj y from rfl, hdz, mul_zero] at h
    have hd0 : dist (y (Fin.last n)) ((hmem.choose) (Fin.last n)) = 0 :=
      le_antisymm h dist_nonneg
    exact dist_eq_zero.mp hd0
  obtain ⟨Φ, hΦlip, hΦeq⟩ := LipschitzOnWith.extend_complex hlip
  refine ⟨Φ, hΦlip, fun y hyS hyP => ?_⟩
  have hmem : proj y ∈ D := ⟨y, ⟨hyS, hyP⟩, rfl⟩
  rw [hsol y hyS hyP]
  exact hΦeq hmem

end Extension

section Package

variable {n : ℕ}

theorem sum_erase_last_le {y z : Fin (n + 1) → ℂ} :
    ∑ k ∈ Finset.univ.erase (Fin.last n), ‖y k - z k‖
      ≤ (n : ℝ) * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc) := by
  classical
  set d : ℝ := dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc) with hd
  have hdnonneg : 0 ≤ d := dist_nonneg
  have hterm : ∀ k ∈ Finset.univ.erase (Fin.last n), ‖y k - z k‖ ≤ d := by
    intro k hk
    have hne : k ≠ Fin.last n := (Finset.mem_erase.mp hk).1
    obtain ⟨k', rfl⟩ : ∃ k' : Fin n, k'.castSucc = k := ⟨k.castPred hne, Fin.castSucc_castPred k hne⟩
    have := dist_le_pi_dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc) k'
    rw [hd]
    calc ‖y k'.castSucc - z k'.castSucc‖ = dist (y k'.castSucc) (z k'.castSucc) :=
          (dist_eq_norm _ _).symm
      _ ≤ _ := this
  calc ∑ k ∈ Finset.univ.erase (Fin.last n), ‖y k - z k‖
      ≤ ∑ _k ∈ Finset.univ.erase (Fin.last n), d := Finset.sum_le_sum hterm
    _ = ((Finset.univ.erase (Fin.last n)).card : ℝ) * d := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (n : ℝ) * d := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        norm_num

/-- **Local implicit function theorem, in Lipschitz form.**  Where the top partial derivative
dominates the deviation of `DP` from a fixed functional, the top coordinate of a solution is given by
a globally Lipschitz function of the lower ones. -/
theorem exists_lipschitz_implicit {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) (hP : ∀ y ∈ S, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) S y)
    {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y ∈ S, ‖P' y - L‖ ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖) :
    ∃ (Φ : (Fin n → ℂ) → ℂ) (K : NNReal), LipschitzWith K Φ ∧
      ∀ y ∈ S, P y = 0 → y (Fin.last n) = Φ (fun k : Fin n => y k.castSucc) := by
  classical
  set c : ℝ := ‖partialCoeff L (Fin.last n)‖ with hc
  set B : ℝ := ∑ k ∈ Finset.univ.erase (Fin.last n), ‖partialCoeff L k‖ with hB
  have hBnonneg : 0 ≤ B := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hcC : 0 < c - C := by linarith
  set M : ℝ := (C + B) * n / (c - C) with hM
  have hMnonneg : 0 ≤ M := by
    rw [hM]
    positivity
  have hgraph : ∀ y ∈ S, P y = 0 → ∀ z ∈ S, P z = 0 →
      dist (y (Fin.last n)) (z (Fin.last n))
        ≤ (Real.toNNReal M : ℝ)
          * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc) := by
    intro y hyS hyP z hzS hzP
    have hest := implicit_lipschitz_estimate hS hP hC hbound (Fin.last n) hyS hzS hyP hzP
    have hsum := sum_erase_last_le (y := y) (z := z)
    have hCB : 0 ≤ C + B := by linarith
    have hchain : (c - C) * ‖y (Fin.last n) - z (Fin.last n)‖
        ≤ (C + B) * ((n : ℝ)
          * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc)) := by
      refine le_trans hest ?_
      exact mul_le_mul_of_nonneg_left hsum hCB
    rw [Real.coe_toNNReal M hMnonneg, hM, dist_eq_norm]
    rw [div_mul_eq_mul_div, le_div_iff₀ hcC]
    calc ‖y (Fin.last n) - z (Fin.last n)‖ * (c - C)
        = (c - C) * ‖y (Fin.last n) - z (Fin.last n)‖ := by ring
      _ ≤ (C + B) * ((n : ℝ)
          * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc)) := hchain
      _ = (C + B) * (n : ℝ)
          * dist (fun k : Fin n => y k.castSucc) (fun k : Fin n => z k.castSucc) := by ring
  obtain ⟨Φ, hΦlip, hΦval⟩ := exists_lipschitz_of_graph hgraph
  exact ⟨Φ, 2 * Real.toNNReal M, hΦlip, hΦval⟩

end Package

end GaloisForLFunctions
