/-
# Brolin boundary tails from disconnected cylinders

This file is the hDisc bridge between the cylinder-univalence engine and the
Brolin/Riesz boundary criterion.  `Brolin.lean` reduces GAP-A to finite
zero-pullback atoms covered by injective cylinder charts; `CylinderUnivalence`
builds those injective charts from stepwise antipodal-freeness.  The lemmas
below splice those two checked components without changing either import lane.
-/
import GaloisForLFunctions.Bottcher.Brolin
import GaloisForLFunctions.Bottcher.CylinderUnivalence

open Complex Set Filter Topology MeasureTheory

namespace Bottcher

/-- Stepwise antipodal-freeness of the forward images of a set gives
injectivity of the full iterate on that set. -/
theorem iterate_injOn_of_forward_antipodalFree
    {c : ℂ} {A : Set ℂ} {n : ℕ}
    (hfree :
      ∀ j < n,
        ∀ z₁ ∈ ((quadratic c)^[j] '' A),
          ∀ z₂ ∈ ((quadratic c)^[j] '' A),
            z₁ = -z₂ → z₁ = z₂) :
    Set.InjOn ((quadratic c)^[n]) A :=
  quadratic_iterate_injOn (c := c) (A := A) n
    (fun j hj =>
      quadratic_injOn (c := c)
        (S := ((quadratic c)^[j] '' A)) (hfree j hj))

/-- Forward containment in open half-planes gives injectivity of the full
iterate on the original cylinder. -/
theorem iterate_injOn_of_forward_halfplane
    {c : ℂ} {A : Set ℂ} {n : ℕ} (a : ℕ → ℂ)
    (hhalf :
      ∀ j < n,
        ∀ z ∈ ((quadratic c)^[j] '' A), 0 < (a j * z).re) :
    Set.InjOn ((quadratic c)^[n]) A :=
  iterate_injOn_of_forward_antipodalFree
    (c := c) (A := A) (n := n)
    (fun j hj => antipodalFree_of_halfplane (a := a j) (hhalf j hj))

/-- A point in a ball whose radius is smaller than the center's distance from
`0` lies in the open half-plane defined by multiplying by the inverse center. -/
theorem invCenter_halfplane_pos_of_norm_sub_lt_norm
    {b w : ℂ} (hb : b ≠ 0) (hw : ‖w - b‖ < ‖b‖) :
    0 < (b⁻¹ * w).re := by
  let u : ℂ := b⁻¹ * (w - b)
  have hdecomp : b⁻¹ * w = 1 + u := by
    calc
      b⁻¹ * w = b⁻¹ * (b + (w - b)) := by ring
      _ = b⁻¹ * b + b⁻¹ * (w - b) := by ring
      _ = 1 + u := by
        rw [inv_mul_cancel₀ hb]
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hu_norm : ‖u‖ < 1 := by
    have hmul : ‖u‖ = ‖b‖⁻¹ * ‖w - b‖ := by
      simp [u, norm_inv]
    rw [hmul]
    exact (inv_mul_lt_iff₀ hbpos).mpr (by simpa using hw)
  have hre_lower : -‖u‖ ≤ u.re := (abs_le.mp (Complex.abs_re_le_norm u)).1
  rw [hdecomp]
  simp only [Complex.add_re, Complex.one_re]
  linarith

/-- Ball-separated forward images give injectivity of the full iterate.  This
is the form produced by shrinking-cylinder estimates: at each time `j`, the
image lies in a ball whose radius is smaller than its center's distance from
the critical point `0`. -/
theorem iterate_injOn_of_forward_ball_separated
    {c : ℂ} {A : Set ℂ} {n : ℕ} (center : ℕ → ℂ)
    (hball :
      ∀ j < n,
        ∀ w ∈ ((quadratic c)^[j] '' A),
          ‖w - center j‖ < ‖center j‖) :
    Set.InjOn ((quadratic c)^[n]) A :=
  iterate_injOn_of_forward_halfplane
    (c := c) (A := A) (n := n) (fun j => (center j)⁻¹)
    (fun j hj w hw => by
      have hlt := hball j hj w hw
      have hcenter_pos : 0 < ‖center j‖ :=
        lt_of_le_of_lt (norm_nonneg _) hlt
      exact
        invCenter_halfplane_pos_of_norm_sub_lt_norm
          (b := center j) (w := w) (norm_pos_iff.mp hcenter_pos) hlt)

/-- Finite singular-tail estimate from a finite cover by forward
antipodal-free cylinders. -/
theorem finiteBrolinSingularTail_le_antipodalFreeCylinderCoverCanonicalClippedLogRangeCost
    {c z : ℂ} {δ : ℝ} {n : ℕ} {ι : Type*}
    {I : Finset ι} {S : ι → Set ℂ}
    (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hfree :
      ∀ i, i ∈ I →
        ∀ j < n,
          ∀ z₁ ∈ ((quadratic c)^[j] '' S i),
            ∀ z₂ ∈ ((quadratic c)^[j] '' S i),
              z₁ = -z₂ → z₁ = z₂)
    (hcover :
      ∀ r ∈ (quadraticPolyIterate c n).roots, ‖z - r‖ < δ →
        ∃ i, i ∈ I ∧ r ∈ S i) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ * (I.card : ℝ) *
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) :=
  finiteBrolinSingularTail_le_cylinderCoverCanonicalClippedLogRangeCost
    (c := c) (z := z) (δ := δ) (n := n)
    (I := I) (S := S) hc hzK
    (fun i hi =>
      iterate_injOn_of_forward_antipodalFree
      (c := c) (A := S i) (n := n) (hfree i hi))
    hcover

/-- Finite singular-tail estimate from a finite cover by cylinders whose
forward images each lie in an open half-plane through `0`. -/
theorem finiteBrolinSingularTail_le_halfplaneCylinderCoverCanonicalClippedLogRangeCost
    {c z : ℂ} {δ : ℝ} {n : ℕ} {ι : Type*}
    {I : Finset ι} {S : ι → Set ℂ} (a : ι → ℕ → ℂ)
    (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hhalf :
      ∀ i, i ∈ I →
        ∀ j < n,
          ∀ w ∈ ((quadratic c)^[j] '' S i),
            0 < (a i j * w).re)
    (hcover :
      ∀ r ∈ (quadraticPolyIterate c n).roots, ‖z - r‖ < δ →
        ∃ i, i ∈ I ∧ r ∈ S i) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ * (I.card : ℝ) *
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) :=
  finiteBrolinSingularTail_le_cylinderCoverCanonicalClippedLogRangeCost
    (c := c) (z := z) (δ := δ) (n := n)
    (I := I) (S := S) hc hzK
    (fun i hi =>
      iterate_injOn_of_forward_halfplane
        (c := c) (A := S i) (n := n) (a i) (hhalf i hi))
    hcover

/-- Finite singular-tail estimate from a finite cover by shrinking cylinders:
each forward image is contained in a ball whose radius is smaller than the
center's distance from `0`. -/
theorem finiteBrolinSingularTail_le_ballSeparatedCylinderCoverCanonicalClippedLogRangeCost
    {c z : ℂ} {δ : ℝ} {n : ℕ} {ι : Type*}
    {I : Finset ι} {S : ι → Set ℂ} (center : ι → ℕ → ℂ)
    (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hball :
      ∀ i, i ∈ I →
        ∀ j < n,
          ∀ w ∈ ((quadratic c)^[j] '' S i),
            ‖w - center i j‖ < ‖center i j‖)
    (hcover :
      ∀ r ∈ (quadraticPolyIterate c n).roots, ‖z - r‖ < δ →
        ∃ i, i ∈ I ∧ r ∈ S i) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ * (I.card : ℝ) *
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) :=
  finiteBrolinSingularTail_le_cylinderCoverCanonicalClippedLogRangeCost
    (c := c) (z := z) (δ := δ) (n := n)
    (I := I) (S := S) hc hzK
    (fun i hi =>
      iterate_injOn_of_forward_ball_separated
        (c := c) (A := S i) (n := n) (center i) (hball i hi))
    hcover

/-- A finite zero-pullback root cannot hit the critical point before its
terminal time in the disconnected case. -/
theorem iterate_ne_zero_of_mem_roots_lt_of_disconnected
    {c r : ℂ} {n j : ℕ} (hc : Disconnected c)
    (hr : r ∈ (quadraticPolyIterate c n).roots) (hj : j < n) :
    (quadratic c)^[j] r ≠ 0 := by
  intro hzero
  have hroot : (quadratic c)^[n] r = 0 := by
    have hisroot : (quadraticPolyIterate c n).IsRoot r :=
      (Polynomial.mem_roots (quadraticPolyIterate_monic c n).ne_zero).mp hr
    simpa [Polynomial.IsRoot.def, quadraticPolyIterate_eval] using hisroot
  have hreturn : (quadratic c)^[n - j] (0 : ℂ) = 0 := by
    have hn : n = (n - j) + j := (Nat.sub_add_cancel (le_of_lt hj)).symm
    calc
      (quadratic c)^[n - j] (0 : ℂ)
          = (quadratic c)^[n - j] ((quadratic c)^[j] r) := by rw [hzero]
      _ = (quadratic c)^[(n - j) + j] r := by
            rw [Function.iterate_add_apply]
      _ = (quadratic c)^[n] r := by rw [← hn]
      _ = 0 := hroot
  exact critical_orbit_ne_zero_of_disconnected hc (Nat.sub_pos_of_lt hj) hreturn

/-- The actual close level-`n` zero-pullback roots admit a singleton
shrinking-cylinder cover.  This is the finite root-level geometry behind the
cylinder-cover estimates: each singleton forward image is centered at its own
orbit point, and those orbit points stay away from `0` until time `n`. -/
theorem finiteBrolinSingularTail_le_singletonRootBallSeparatedCoverCanonicalClippedLogRangeCost
    {c z : ℂ} {δ : ℝ} {n : ℕ}
    (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    finiteBrolinSingularTail c z δ n ≤
      (2 ^ n : ℝ)⁻¹ *
        (((quadraticPolyIterate c n).roots.filter
          (fun r => ‖z - r‖ < δ)).card : ℝ) *
        max 0
          (Real.log δ - Real.log (finiteBrolinRootSeparation c z n)) := by
  classical
  let Rm : Multiset ℂ :=
    (quadraticPolyIterate c n).roots.filter (fun r => ‖z - r‖ < δ)
  let I : Finset ℂ := Rm.toFinset
  let S : ℂ → Set ℂ := fun i => {i}
  let center : ℂ → ℕ → ℂ := fun i j => (quadratic c)^[j] i
  have hnodup : Rm.Nodup :=
    (roots_nodup_quadraticPolyIterate_of_disconnected hc n).filter
      (fun r => ‖z - r‖ < δ)
  have hIcard : I.card = Rm.card := by
    change Rm.toFinset.card = Rm.card
    rw [Multiset.toFinset_card_of_nodup hnodup]
  have hball :
      ∀ i, i ∈ I →
        ∀ j < n,
          ∀ w ∈ ((quadratic c)^[j] '' S i),
            ‖w - center i j‖ < ‖center i j‖ := by
    intro i hi j hj w hw
    have hiRm : i ∈ Rm := by
      change i ∈ Rm.toFinset at hi
      exact Multiset.mem_toFinset.mp hi
    rcases Multiset.mem_filter.mp hiRm with ⟨hiroot, _hiclose⟩
    rcases hw with ⟨x, hxS, rfl⟩
    have hxi : x = i := by simpa [S] using hxS
    subst x
    have hnz :
        (quadratic c)^[j] i ≠ 0 :=
      iterate_ne_zero_of_mem_roots_lt_of_disconnected
        (c := c) (r := i) (n := n) (j := j) hc hiroot hj
    have hpos : 0 < ‖(quadratic c)^[j] i‖ := norm_pos_iff.mpr hnz
    simpa [center]
  have hcover :
      ∀ r ∈ (quadraticPolyIterate c n).roots, ‖z - r‖ < δ →
        ∃ i, i ∈ I ∧ r ∈ S i := by
    intro r hr hclose
    refine ⟨r, ?_, ?_⟩
    · change r ∈ Rm.toFinset
      exact Multiset.mem_toFinset.mpr
        (Multiset.mem_filter.mpr ⟨hr, hclose⟩)
    · simp [S]
  have htail :=
    finiteBrolinSingularTail_le_ballSeparatedCylinderCoverCanonicalClippedLogRangeCost
      (c := c) (z := z) (δ := δ) (n := n)
      (I := I) (S := S) (center := center) hc hzK hball hcover
  rw [hIcard] at htail
  simpa [Rm] using htail

/-- hDisc closure from forward antipodal-free cylinder covers and the exact
clipped count estimate. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_antipodalFreeCylinderCoverClippedLogRange_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              ∃ I : Finset ι, ∃ S : ι → Set ℂ,
                (∀ i, i ∈ I →
                  ∀ j < brolinLimitSubsequence c k,
                    ∀ z₁ ∈ ((quadratic c)^[j] '' S i),
                      ∀ z₂ ∈ ((quadratic c)^[j] '' S i),
                        z₁ = -z₂ → z₁ = z₂) ∧
                (∀ r ∈ (quadraticPolyIterate c
                    (brolinLimitSubsequence c k)).roots,
                  ‖z - r‖ < δ →
                    ∃ i, i ∈ I ∧ r ∈ S i) ∧
                (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹ *
                  (I.card : ℝ) *
                  max 0
                    (Real.log δ -
                      Real.log
                        (finiteBrolinRootSeparation c z
                          (brolinLimitSubsequence c k))) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_cylinderCoverClippedLogRange_control
    (c := c) (ι := ι) hc
  intro z hzK hint ε hε
  rcases hgeom z hzK hint ε hε with ⟨δ, hδpos, hδle, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hgeom_event] with k hk
  rcases hk with ⟨I, S, hfree, hcover, hbound⟩
  refine ⟨I, S, ?_, hcover, hbound⟩
  intro i hi
  exact
    iterate_injOn_of_forward_antipodalFree
      (c := c) (A := S i) (n := brolinLimitSubsequence c k)
      (hfree i hi)

/-- hDisc closure from forward half-plane cylinder covers and the exact
clipped count estimate. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_halfplaneCylinderCoverClippedLogRange_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              ∃ I : Finset ι, ∃ S : ι → Set ℂ, ∃ a : ι → ℕ → ℂ,
                (∀ i, i ∈ I →
                  ∀ j < brolinLimitSubsequence c k,
                    ∀ w ∈ ((quadratic c)^[j] '' S i),
                      0 < (a i j * w).re) ∧
                (∀ r ∈ (quadraticPolyIterate c
                    (brolinLimitSubsequence c k)).roots,
                  ‖z - r‖ < δ →
                    ∃ i, i ∈ I ∧ r ∈ S i) ∧
                (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹ *
                  (I.card : ℝ) *
                  max 0
                    (Real.log δ -
                      Real.log
                        (finiteBrolinRootSeparation c z
                          (brolinLimitSubsequence c k))) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_cylinderCoverClippedLogRange_control
    (c := c) (ι := ι) hc
  intro z hzK hint ε hε
  rcases hgeom z hzK hint ε hε with ⟨δ, hδpos, hδle, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hgeom_event] with k hk
  rcases hk with ⟨I, S, a, hhalf, hcover, hbound⟩
  refine ⟨I, S, ?_, hcover, hbound⟩
  intro i hi
  exact
    iterate_injOn_of_forward_halfplane
      (c := c) (A := S i) (n := brolinLimitSubsequence c k)
      (a i) (hhalf i hi)

/-- hDisc closure from shrinking-ball cylinder covers and the exact clipped
count estimate. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_ballSeparatedCylinderCoverClippedLogRange_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∀ᶠ k in atTop,
              ∃ I : Finset ι, ∃ S : ι → Set ℂ,
                ∃ center : ι → ℕ → ℂ,
                (∀ i, i ∈ I →
                  ∀ j < brolinLimitSubsequence c k,
                    ∀ w ∈ ((quadratic c)^[j] '' S i),
                      ‖w - center i j‖ < ‖center i j‖) ∧
                (∀ r ∈ (quadraticPolyIterate c
                    (brolinLimitSubsequence c k)).roots,
                  ‖z - r‖ < δ →
                    ∃ i, i ∈ I ∧ r ∈ S i) ∧
                (2 ^ (brolinLimitSubsequence c k) : ℝ)⁻¹ *
                  (I.card : ℝ) *
                  max 0
                    (Real.log δ -
                      Real.log
                        (finiteBrolinRootSeparation c z
                          (brolinLimitSubsequence c k))) ≤ ε) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply gapAMu_hasGreenPotentialRepresentation_of_cylinderCoverClippedLogRange_control
    (c := c) (ι := ι) hc
  intro z hzK hint ε hε
  rcases hgeom z hzK hint ε hε with ⟨δ, hδpos, hδle, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, ?_⟩
  filter_upwards [hgeom_event] with k hk
  rcases hk with ⟨I, S, center, hball, hcover, hbound⟩
  refine ⟨I, S, ?_, hcover, hbound⟩
  intro i hi
  exact
    iterate_injOn_of_forward_ball_separated
      (c := c) (A := S i) (n := brolinLimitSubsequence c k)
      (center i) (hball i hi)

/-- hDisc closure from forward antipodal-free cylinder covers whose count
grows like `O(qⁿ)` for some `q < 2`, plus exponential finite separation. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_antipodalFreeCylinderCover_subtwoExponentialSeparation_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∃ A : ℝ, 0 < A ∧
              ∃ C : ℝ, 0 ≤ C ∧
                ∃ q : ℝ, 0 ≤ q ∧ q < 2 ∧
                  ∀ᶠ k in atTop,
                    ∃ I : Finset ι, ∃ S : ι → Set ℂ,
                      (I.card : ℝ) ≤
                        C * q ^ (brolinLimitSubsequence c k) ∧
                      (∀ i, i ∈ I →
                        ∀ j < brolinLimitSubsequence c k,
                          ∀ z₁ ∈ ((quadratic c)^[j] '' S i),
                            ∀ z₂ ∈ ((quadratic c)^[j] '' S i),
                              z₁ = -z₂ → z₁ = z₂) ∧
                      (∀ r ∈ (quadraticPolyIterate c
                          (brolinLimitSubsequence c k)).roots,
                        ‖z - r‖ < δ →
                          ∃ i, i ∈ I ∧ r ∈ S i) ∧
                      Real.exp
                        (-(A * (brolinLimitSubsequence c k : ℝ))) ≤
                        finiteBrolinRootSeparation c z
                          (brolinLimitSubsequence c k)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply
    gapAMu_hasGreenPotentialRepresentation_of_cylinderCover_subtwoExponentialSeparation_control
      (c := c) (ι := ι) hc
  intro z hzK hint
  rcases hgeom z hzK hint with
    ⟨δ, hδpos, hδle, A, hApos, C, hCnonneg, q,
      hqnonneg, hqlt, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, A, hApos, C, hCnonneg, q,
    hqnonneg, hqlt, ?_⟩
  filter_upwards [hgeom_event] with k hk
  rcases hk with ⟨I, S, hIcard, hfree, hcover, hsep⟩
  refine ⟨I, S, hIcard, ?_, hcover, hsep⟩
  intro i hi
  exact
    iterate_injOn_of_forward_antipodalFree
      (c := c) (A := S i) (n := brolinLimitSubsequence c k)
      (hfree i hi)

/-- hDisc closure from forward half-plane cylinder covers whose count grows
like `O(qⁿ)` for some `q < 2`, plus exponential finite separation. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_halfplaneCylinderCover_subtwoExponentialSeparation_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∃ A : ℝ, 0 < A ∧
              ∃ C : ℝ, 0 ≤ C ∧
                ∃ q : ℝ, 0 ≤ q ∧ q < 2 ∧
                  ∀ᶠ k in atTop,
                    ∃ I : Finset ι, ∃ S : ι → Set ℂ,
                      ∃ a : ι → ℕ → ℂ,
                      (I.card : ℝ) ≤
                        C * q ^ (brolinLimitSubsequence c k) ∧
                      (∀ i, i ∈ I →
                        ∀ j < brolinLimitSubsequence c k,
                          ∀ w ∈ ((quadratic c)^[j] '' S i),
                            0 < (a i j * w).re) ∧
                      (∀ r ∈ (quadraticPolyIterate c
                          (brolinLimitSubsequence c k)).roots,
                        ‖z - r‖ < δ →
                          ∃ i, i ∈ I ∧ r ∈ S i) ∧
                      Real.exp
                        (-(A * (brolinLimitSubsequence c k : ℝ))) ≤
                        finiteBrolinRootSeparation c z
                          (brolinLimitSubsequence c k)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply
    gapAMu_hasGreenPotentialRepresentation_of_cylinderCover_subtwoExponentialSeparation_control
      (c := c) (ι := ι) hc
  intro z hzK hint
  rcases hgeom z hzK hint with
    ⟨δ, hδpos, hδle, A, hApos, C, hCnonneg, q,
      hqnonneg, hqlt, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, A, hApos, C, hCnonneg, q,
    hqnonneg, hqlt, ?_⟩
  filter_upwards [hgeom_event] with k hk
  rcases hk with ⟨I, S, a, hIcard, hhalf, hcover, hsep⟩
  refine ⟨I, S, hIcard, ?_, hcover, hsep⟩
  intro i hi
  exact
    iterate_injOn_of_forward_halfplane
      (c := c) (A := S i) (n := brolinLimitSubsequence c k)
      (a i) (hhalf i hi)

/-- hDisc closure from shrinking-ball cylinder covers whose count grows like
`O(qⁿ)` for some `q < 2`, plus exponential finite separation. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_ballSeparatedCylinderCover_subtwoExponentialSeparation_control
    {c : ℂ} {ι : Type*} (hc : Disconnected c)
    (hgeom :
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
          ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
            ∃ A : ℝ, 0 < A ∧
              ∃ C : ℝ, 0 ≤ C ∧
                ∃ q : ℝ, 0 ≤ q ∧ q < 2 ∧
                  ∀ᶠ k in atTop,
                    ∃ I : Finset ι, ∃ S : ι → Set ℂ,
                      ∃ center : ι → ℕ → ℂ,
                      (I.card : ℝ) ≤
                        C * q ^ (brolinLimitSubsequence c k) ∧
                      (∀ i, i ∈ I →
                        ∀ j < brolinLimitSubsequence c k,
                          ∀ w ∈ ((quadratic c)^[j] '' S i),
                            ‖w - center i j‖ < ‖center i j‖) ∧
                      (∀ r ∈ (quadraticPolyIterate c
                          (brolinLimitSubsequence c k)).roots,
                        ‖z - r‖ < δ →
                          ∃ i, i ∈ I ∧ r ∈ S i) ∧
                      Real.exp
                        (-(A * (brolinLimitSubsequence c k : ℝ))) ≤
                        finiteBrolinRootSeparation c z
                          (brolinLimitSubsequence c k)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  apply
    gapAMu_hasGreenPotentialRepresentation_of_cylinderCover_subtwoExponentialSeparation_control
      (c := c) (ι := ι) hc
  intro z hzK hint
  rcases hgeom z hzK hint with
    ⟨δ, hδpos, hδle, A, hApos, C, hCnonneg, q,
      hqnonneg, hqlt, hgeom_event⟩
  refine ⟨δ, hδpos, hδle, A, hApos, C, hCnonneg, q,
    hqnonneg, hqlt, ?_⟩
  filter_upwards [hgeom_event] with k hk
  rcases hk with ⟨I, S, center, hIcard, hball, hcover, hsep⟩
  refine ⟨I, S, hIcard, ?_, hcover, hsep⟩
  intro i hi
  exact
    iterate_injOn_of_forward_ball_separated
      (c := c) (A := S i) (n := brolinLimitSubsequence c k)
      (center i) (hball i hi)

end Bottcher
