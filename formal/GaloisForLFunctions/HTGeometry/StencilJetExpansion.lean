import GaloisForLFunctions.HTGeometry.DomainJetRelationLocus
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference

/-!
# Jet expansion of a finite translation stencil

A finite translation stencil `A_h F (z) = ∑ l, c l * F (z + λ l * h)` has, in the shift variable,
the Taylor expansion

```text
(A_h F)^{(j)} (z) = ∑ m (h ^ m / m !) * M m * F^{(j+m)} (z),   M m = ∑ l c l * (λ l) ^ m.
```

Every jet order sees the *same* moments `M m`, so if the first nonzero moment is `M k`, then every
jet coordinate of the stencil vanishes to order exactly `k` in `h` and the uniformly normalized
family `h ↦ h ^ (-k) (A_h F)^{(j)}(z)` converges to `M k / k ! * F^{(j+k)}(z)`.

This module supplies the two ingredients: a local affine chain rule for iterated derivatives, and
the moment formula for the shift jets of the stencil.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology

noncomputable section

/-! ## A local affine chain rule for iterated derivatives -/

theorem iteratedDeriv_iteratedDeriv_stencilJetExpansion (m j : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv m (iteratedDeriv j f) = iteratedDeriv (m + j) f := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ', ih (f := deriv f), ← iteratedDeriv_succ']
      congr 1

theorem iteratedDeriv_comp_affine_on {u : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hu : AnalyticOnNhd ℂ u W) (a lam : ℂ) :
    ∀ (m : ℕ) {h : ℂ}, a + lam * h ∈ W →
      iteratedDeriv m (fun t => u (a + lam * t)) h = lam ^ m * iteratedDeriv m u (a + lam * h) := by
  intro m
  induction m with
  | zero => intro h _; simp
  | succ m ih =>
      intro h hh
      have hVopen : IsOpen ((fun t : ℂ => a + lam * t) ⁻¹' W) := hW.preimage (by fun_prop)
      have hhV : h ∈ (fun t : ℂ => a + lam * t) ⁻¹' W := hh
      have hev : iteratedDeriv m (fun t => u (a + lam * t))
          =ᶠ[nhds h] (fun t => lam ^ m * iteratedDeriv m u (a + lam * t)) := by
        filter_upwards [hVopen.mem_nhds hhV] with t ht using ih ht
      have hg : AnalyticAt ℂ (iteratedDeriv m u) (a + lam * h) :=
        analyticOnNhd_iteratedDeriv hu m _ hh
      have hinner : HasDerivAt (fun t : ℂ => a + lam * t) lam h := by
        simpa using ((hasDerivAt_id h).const_mul lam).const_add a
      have hchain0 : HasDerivAt ((iteratedDeriv m u) ∘ fun t : ℂ => a + lam * t)
          (deriv (iteratedDeriv m u) (a + lam * h) * lam) h :=
        HasDerivAt.comp h (hg.differentiableAt.hasDerivAt) hinner
      have hchain : HasDerivAt (fun t : ℂ => iteratedDeriv m u (a + lam * t))
          (deriv (iteratedDeriv m u) (a + lam * h) * lam) h := hchain0
      have hfinal : HasDerivAt (fun t : ℂ => lam ^ m * iteratedDeriv m u (a + lam * t))
          (lam ^ m * (deriv (iteratedDeriv m u) (a + lam * h) * lam)) h := hchain.const_mul _
      rw [iteratedDeriv_succ, hev.deriv_eq, hfinal.deriv]
      rw [show iteratedDeriv (m + 1) u = deriv (iteratedDeriv m u) from
        (iteratedDeriv_succ (n := m) (f := u))]
      ring

/-! ## The stencil and its moments -/

/-- The `m`-th moment of a finite translation stencil. -/
def stencilMoment {J : ℕ} (c lam : Fin J → ℂ) (m : ℕ) : ℂ := ∑ l, c l * (lam l) ^ m

/-- A finite translation stencil applied to `F` at shift `h`. -/
def stencilApply {J : ℕ} (F : ℂ → ℂ) (c lam : Fin J → ℂ) (h : ℂ) : ℂ → ℂ :=
  fun z => ∑ l, c l * F (z + lam l * h)

/-- The shift-variable profile of one jet coordinate of the stencil. -/
def stencilShiftProfile {J : ℕ} (F : ℂ → ℂ) (c lam : Fin J → ℂ) (a : ℂ) (j : ℕ) : ℂ → ℂ :=
  fun h => ∑ l, c l * iteratedDeriv j F (a + lam l * h)

theorem analyticAt_stencilShiftProfile {J : ℕ} {F : ℂ → ℂ} {W : Set ℂ}
    (hF : AnalyticOnNhd ℂ F W) (c lam : Fin J → ℂ) (a : ℂ) (j : ℕ) {h : ℂ}
    (hmem : ∀ l, a + lam l * h ∈ W) :
    AnalyticAt ℂ (stencilShiftProfile F c lam a j) h := by
  have hterm : ∀ l : Fin J,
      AnalyticAt ℂ (fun t : ℂ => c l * iteratedDeriv j F (a + lam l * t)) h := by
    intro l
    refine analyticAt_const.mul ?_
    have hd : AnalyticAt ℂ (iteratedDeriv j F) (a + lam l * h) :=
      analyticOnNhd_iteratedDeriv hF j _ (hmem l)
    have hinner : AnalyticAt ℂ (fun t : ℂ => a + lam l * t) h :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    exact AnalyticAt.comp (𝕜 := ℂ) (g := iteratedDeriv j F)
      (f := fun t : ℂ => a + lam l * t) (x := h) hd hinner
  have heq : stencilShiftProfile F c lam a j
      = ∑ l : Fin J, fun t : ℂ => c l * iteratedDeriv j F (a + lam l * t) := by
    funext t
    simp [stencilShiftProfile, Finset.sum_apply]
  rw [heq]
  exact Finset.analyticAt_sum _ fun l _ => hterm l

/-- **The moment formula.**  The `m`-th shift derivative at `h = 0` of the `j`-th jet profile of a
finite translation stencil is the `m`-th stencil moment times the `(j+m)`-th derivative of the
source. -/
theorem iteratedDeriv_stencilShiftProfile_zero {J : ℕ} {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) (c lam : Fin J → ℂ) {a : ℂ} (ha : a ∈ W) (j m : ℕ) :
    iteratedDeriv m (stencilShiftProfile F c lam a j) 0
      = stencilMoment c lam m * iteratedDeriv (j + m) F a := by
  classical
  have hterm : ∀ l : Fin J, ContDiffAt ℂ (m : ℕ)
      (fun t : ℂ => c l * iteratedDeriv j F (a + lam l * t)) 0 := by
    intro l
    have hmem : a + lam l * (0 : ℂ) ∈ W := by simpa using ha
    have hd : AnalyticAt ℂ (iteratedDeriv j F) (a + lam l * 0) :=
      analyticOnNhd_iteratedDeriv hF j _ hmem
    have hinner : AnalyticAt ℂ (fun t : ℂ => a + lam l * t) 0 :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    have hcomp : AnalyticAt ℂ (iteratedDeriv j F ∘ fun t : ℂ => a + lam l * t) 0 :=
      AnalyticAt.comp (𝕜 := ℂ) (g := iteratedDeriv j F)
        (f := fun t : ℂ => a + lam l * t) (x := 0) hd hinner
    exact (analyticAt_const.mul hcomp).contDiffAt
  have hsum : stencilShiftProfile F c lam a j
      = ∑ l : Fin J, fun t : ℂ => c l * iteratedDeriv j F (a + lam l * t) := by
    funext t
    simp [stencilShiftProfile, Finset.sum_apply]
  rw [hsum, iteratedDeriv_sum (fun l _ => hterm l)]
  have hone : ∀ l : Fin J,
      iteratedDeriv m (fun t : ℂ => c l * iteratedDeriv j F (a + lam l * t)) 0
        = c l * ((lam l) ^ m * iteratedDeriv (m + j) F a) := by
    intro l
    have hmem : a + lam l * (0 : ℂ) ∈ W := by simpa using ha
    have hinner : AnalyticAt ℂ (fun t : ℂ => a + lam l * t) 0 :=
      analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    have hd : AnalyticAt ℂ (iteratedDeriv j F) (a + lam l * 0) :=
      analyticOnNhd_iteratedDeriv hF j _ hmem
    have hcomp : ContDiffAt ℂ (m : ℕ)
        (fun t : ℂ => iteratedDeriv j F (a + lam l * t)) 0 := by
      have : AnalyticAt ℂ (iteratedDeriv j F ∘ fun t : ℂ => a + lam l * t) 0 :=
        AnalyticAt.comp (𝕜 := ℂ) (g := iteratedDeriv j F)
          (f := fun t : ℂ => a + lam l * t) (x := 0) hd hinner
      exact this.contDiffAt
    rw [iteratedDeriv_const_mul _ hcomp]
    congr 1
    have haff := iteratedDeriv_comp_affine_on hW (analyticOnNhd_iteratedDeriv hF j) a (lam l) m
      (h := (0 : ℂ)) hmem
    rw [haff, iteratedDeriv_iteratedDeriv_stencilJetExpansion]
    simp
  rw [Finset.sum_congr rfl fun l _ => hone l, stencilMoment, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Nat.add_comm m j]
  ring


/-! ## The `k`-fold removable division of the shift profile -/

/-- The `k`-fold removable divided slope at the origin. -/
def dslopeIterZero (g : ℂ → ℂ) (k : ℕ) : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[k] g

@[simp] theorem dslopeIterZero_zero (g : ℂ → ℂ) : dslopeIterZero g 0 = g := rfl

theorem dslopeIterZero_succ (g : ℂ → ℂ) (k : ℕ) :
    dslopeIterZero g (k + 1) = dslope (dslopeIterZero g k) 0 := by
  simp [dslopeIterZero, Function.iterate_succ_apply']

theorem analyticAt_dslopeIterZero {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    AnalyticAt ℂ (dslopeIterZero g k) 0 := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      rw [dslopeIterZero_succ]
      obtain ⟨p, hp⟩ := ih
      exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem dslopeIterZero_self {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    dslopeIterZero g k 0 = iteratedDeriv k g 0 / (k.factorial : ℂ) :=
  _root_.HTGeometry.iterate_dslope_self_eq_iteratedDeriv_div_factorial hg k

/-- With vanishing lower center values the `k`-fold removable slope is the honest quotient. -/
theorem dslopeIterZero_of_ne {g : ℂ → ℂ} {k : ℕ}
    (hvanish : ∀ m, m < k → dslopeIterZero g m 0 = 0) {h : ℂ} (hh : h ≠ 0) :
    dslopeIterZero g k h = g h / h ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hlow : ∀ m, m < k → dslopeIterZero g m 0 = 0 := fun m hm =>
        hvanish m (Nat.lt_succ_of_lt hm)
      have hk : dslopeIterZero g k 0 = 0 := hvanish k (Nat.lt_succ_self k)
      rw [dslopeIterZero_succ, dslope_of_ne _ hh, slope_def_field, hk, sub_zero, ih hlow,
        sub_zero, pow_succ]
      field_simp

/-! ## The normalized stencil profile -/

/-- The `k`-fold removable division of the `j`-th stencil shift profile. -/
def stencilNormalizedProfile {J : ℕ} (F : ℂ → ℂ) (c lam : Fin J → ℂ) (a : ℂ) (j k : ℕ) : ℂ → ℂ :=
  dslopeIterZero (stencilShiftProfile F c lam a j) k

theorem analyticAt_stencilNormalizedProfile {J : ℕ} {F : ℂ → ℂ} {W : Set ℂ}
    (hF : AnalyticOnNhd ℂ F W) (c lam : Fin J → ℂ) {a : ℂ} (ha : a ∈ W) (j k : ℕ) :
    AnalyticAt ℂ (stencilNormalizedProfile F c lam a j k) 0 := by
  refine analyticAt_dslopeIterZero ?_ k
  exact analyticAt_stencilShiftProfile hF c lam a j (fun l => by simpa using ha)

theorem stencilNormalizedProfile_center {J : ℕ} {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) (c lam : Fin J → ℂ) {a : ℂ} (ha : a ∈ W) (j k : ℕ) :
    stencilNormalizedProfile F c lam a j k 0
      = stencilMoment c lam k * iteratedDeriv (j + k) F a / (k.factorial : ℂ) := by
  rw [stencilNormalizedProfile,
    dslopeIterZero_self (analyticAt_stencilShiftProfile hF c lam a j
      (fun l => by simpa using ha)) k,
    iteratedDeriv_stencilShiftProfile_zero hW hF c lam ha j k]

/-- Below the first nonzero moment every center value of the removable chain vanishes. -/
theorem stencilNormalizedProfile_center_eq_zero {J : ℕ} {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : AnalyticOnNhd ℂ F W) {c lam : Fin J → ℂ} {a : ℂ} (ha : a ∈ W) (j : ℕ) {m : ℕ}
    (hm : stencilMoment c lam m = 0) :
    stencilNormalizedProfile F c lam a j m 0 = 0 := by
  rw [stencilNormalizedProfile_center hW hF c lam ha j m, hm, zero_mul, zero_div]

end

end GaloisForLFunctions.HTGeometry
