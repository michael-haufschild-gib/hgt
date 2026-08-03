import GaloisForLFunctions.HTGeometry.ExponentialJetOpenness
import GaloisForLFunctions.HTGeometry.InversionJetMap

/-!
# The Cayley outer jet chart is open

The Cayley exponential `chi(w) = exp((w - i)/(w + i))` factors as `exp` after an affine map after a
reciprocal after an affine map, because `(w - i)/(w + i) = 1 - 2i/(w + i)`.  Each factor acts on jet
packets by a map already known to carry neighbourhoods to neighbourhoods: affine jet maps are linear
isomorphisms, the reciprocal jet map is a continuous involution, and the exponential jet map is
triangular with nonvanishing diagonal.

So the whole chart is open, with no implicit function theorem and no Faa di Bruno formula.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A map with a continuous right inverse through the base point carries neighbourhoods to
neighbourhoods. -/
theorem image_mem_nhds_of_continuousAt_rightInverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {Φ : X → Y} {Ψ : Y → X} {y : X} {N : Set X} (hN : N ∈ nhds y)
    (hΨ : ContinuousAt Ψ (Φ y)) (hΨy : Ψ (Φ y) = y) (hΦΨ : ∀ w, Φ (Ψ w) = w) :
    Φ '' N ∈ nhds (Φ y) := by
  have hpre : Ψ ⁻¹' N ∈ nhds (Φ y) := by
    refine hΨ ?_
    rw [hΨy]
    exact hN
  refine Filter.mem_of_superset hpre ?_
  intro w hw
  exact ⟨Ψ w, hw, hΦΨ w⟩

/-! ## Affine jet maps -/

/-- The jets of `a f + b`. -/
def affJetScalar (a b : ℂ) (y : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 0 then a * y 0 + b else a * y k

theorem affJetScalar_iteratedDeriv (a b : ℂ) {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ (⊤ : ℕ∞) f z) (k : ℕ) :
    iteratedDeriv k (fun w => a * f w + b) z
      = affJetScalar a b (fun j => iteratedDeriv j f z) k := by
  have hfk : ContDiffAt ℂ ((k : ℕ) : ℕ∞) f z :=
    hf.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
  have hmul : ContDiffAt ℂ ((k : ℕ) : ℕ∞) (fun w => a * f w) z := contDiffAt_const.mul hfk
  have hsum : (fun w => a * f w + b) = (fun w => a * f w) + fun _ => b := rfl
  rw [affJetScalar, hsum, iteratedDeriv_add hmul contDiffAt_const,
    iteratedDeriv_const_mul a hfk]
  cases k with
  | zero => simp
  | succ k =>
      simp [iteratedDeriv_succ']

@[simp]
theorem affJetScalar_apply_zero (a b : ℂ) (y : ℕ → ℂ) : affJetScalar a b y 0 = a * y 0 + b := by
  simp [affJetScalar]

theorem affJetScalar_apply_of_ne (a b : ℂ) (y : ℕ → ℂ) {k : ℕ} (hk : k ≠ 0) :
    affJetScalar a b y k = a * y k := by
  simp [affJetScalar, hk]

theorem continuous_affJetScalar (a b : ℂ) :
    Continuous fun v : ℕ → ℂ => fun k => affJetScalar a b v k := by
  refine continuous_pi fun k => ?_
  by_cases hk : k = 0
  · subst hk
    simp only [affJetScalar_apply_zero]
    exact (continuous_const.mul (continuous_apply (0 : ℕ))).add continuous_const
  · simp only [affJetScalar_apply_of_ne a b _ hk]
    exact continuous_const.mul (continuous_apply k)

theorem affJetScalar_affJetScalar {a b : ℂ} (ha : a ≠ 0) (v : ℕ → ℂ) (k : ℕ) :
    affJetScalar a b (fun j => affJetScalar a⁻¹ (-(b / a)) v j) k = v k := by
  by_cases hk : k = 0
  · subst hk
    simp only [affJetScalar_apply_zero]
    field_simp
    ring
  · simp only [affJetScalar_apply_of_ne _ _ _ hk]
    field_simp

theorem affJetScalar_affJetScalar' {a b : ℂ} (ha : a ≠ 0) (v : ℕ → ℂ) (k : ℕ) :
    affJetScalar a⁻¹ (-(b / a)) (fun j => affJetScalar a b v j) k = v k := by
  by_cases hk : k = 0
  · subst hk
    simp only [affJetScalar_apply_zero]
    field_simp
    ring
  · simp only [affJetScalar_apply_of_ne _ _ _ hk]
    field_simp

/-- **Affine jet maps carry neighbourhoods to neighbourhoods.** -/
theorem affJetScalar_image_mem_nhds {a b : ℂ} (ha : a ≠ 0) (y : ℕ → ℂ) {N : Set (ℕ → ℂ)}
    (hN : N ∈ nhds y) :
    (fun v : ℕ → ℂ => fun k => affJetScalar a b v k) '' N
      ∈ nhds (fun k => affJetScalar a b y k) := by
  refine image_mem_nhds_of_continuousAt_rightInverse
    (Φ := fun v : ℕ → ℂ => fun k => affJetScalar a b v k)
    (Ψ := fun v : ℕ → ℂ => fun k => affJetScalar a⁻¹ (-(b / a)) v k) hN
    ((continuous_affJetScalar a⁻¹ (-(b / a))).continuousAt) ?_ ?_
  · funext k
    exact affJetScalar_affJetScalar' ha y k
  · intro w
    funext k
    exact affJetScalar_affJetScalar ha w k

/-! ## The Cayley outer jet chart -/

/-- The jets of `chi ∘ f`, assembled from the affine, reciprocal and exponential jet maps. -/
def chiJetScalar (y : ℕ → ℂ) : ℕ → ℂ :=
  expJetScalar
    (fun j => affJetScalar (-(2 * Complex.I)) 1
      (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I y m) l) j)

/-- **The Cayley outer jet chart carries neighbourhoods to neighbourhoods.** -/
theorem chiJetScalar_image_mem_nhds {y : ℕ → ℂ} (hy : y 0 + Complex.I ≠ 0) {N : Set (ℕ → ℂ)}
    (hN : N ∈ nhds y) :
    (fun v : ℕ → ℂ => fun k => chiJetScalar v k) '' N ∈ nhds (fun k => chiJetScalar y k) := by
  classical
  set A₁ : (ℕ → ℂ) → (ℕ → ℂ) := fun v => fun k => affJetScalar 1 Complex.I v k with hA₁
  set R : (ℕ → ℂ) → (ℕ → ℂ) := fun v => fun k => invJetScalar v k with hR
  set A₂ : (ℕ → ℂ) → (ℕ → ℂ) := fun v => fun k => affJetScalar (-(2 * Complex.I)) 1 v k with hA₂
  set E : (ℕ → ℂ) → (ℕ → ℂ) := fun v => fun k => expJetScalar v k with hE
  have hA₁y : A₁ y 0 ≠ 0 := by
    simp only [hA₁, affJetScalar_apply_zero, one_mul]
    exact hy
  have h1 : A₁ '' N ∈ nhds (A₁ y) := affJetScalar_image_mem_nhds one_ne_zero y hN
  have h2 : R '' (A₁ '' N) ∈ nhds (R (A₁ y)) := invJetScalar_image_mem_nhds hA₁y h1
  have h3 : A₂ '' (R '' (A₁ '' N)) ∈ nhds (A₂ (R (A₁ y))) := by
    refine affJetScalar_image_mem_nhds ?_ _ h2
    simp only [ne_eq, neg_eq_zero, mul_eq_zero]
    push Not
    exact ⟨two_ne_zero, Complex.I_ne_zero⟩
  have h4 : E '' (A₂ '' (R '' (A₁ '' N))) ∈ nhds (E (A₂ (R (A₁ y)))) :=
    expJetScalar_image_mem_nhds _ h3
  have himg : (fun v : ℕ → ℂ => fun k => chiJetScalar v k) '' N
      = E '' (A₂ '' (R '' (A₁ '' N))) := by
    rw [← Set.image_comp, ← Set.image_comp, ← Set.image_comp]
    rfl
  have hval : (fun k => chiJetScalar y k) = E (A₂ (R (A₁ y))) := rfl
  rw [himg, hval]
  exact h4

/-- **The chart computes the derivatives of the Cayley exponential.** -/
theorem chiJetScalar_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℂ (⊤ : ℕ∞) f U) (hne : ∀ w ∈ U, f w + Complex.I ≠ 0) {z : ℂ} (hz : z ∈ U)
    (k : ℕ) :
    iteratedDeriv k (fun w => Complex.exp ((f w - Complex.I) / (f w + Complex.I))) z
      = chiJetScalar (fun j => iteratedDeriv j f z) k := by
  set f₁ : ℂ → ℂ := fun w => 1 * f w + Complex.I with hf₁def
  set f₂ : ℂ → ℂ := fun w => (f₁ w)⁻¹ with hf₂def
  set f₃ : ℂ → ℂ := fun w => -(2 * Complex.I) * f₂ w + 1 with hf₃def
  have hf₁ : ContDiffOn ℂ (⊤ : ℕ∞) f₁ U := (contDiffOn_const.mul hf).add contDiffOn_const
  have hf₁ne : ∀ w ∈ U, f₁ w ≠ 0 := by
    intro w hw
    simpa [hf₁def] using hne w hw
  have hf₂ : ContDiffOn ℂ (⊤ : ℕ∞) f₂ U := hf₁.inv hf₁ne
  have hf₃ : ContDiffOn ℂ (⊤ : ℕ∞) f₃ U := (contDiffOn_const.mul hf₂).add contDiffOn_const
  have j₁ : ∀ j, iteratedDeriv j f₁ z
      = affJetScalar 1 Complex.I (fun l => iteratedDeriv l f z) j :=
    fun j => affJetScalar_iteratedDeriv 1 Complex.I (hf.contDiffAt (hU.mem_nhds hz)) j
  have j₂ : ∀ j, iteratedDeriv j f₂ z = invJetScalar (fun l => iteratedDeriv l f₁ z) j :=
    fun j => invJetScalar_iteratedDeriv hU hf₁ hf₁ne hz j
  have j₃ : ∀ j, iteratedDeriv j f₃ z
      = affJetScalar (-(2 * Complex.I)) 1 (fun l => iteratedDeriv l f₂ z) j :=
    fun j => affJetScalar_iteratedDeriv _ _ (hf₂.contDiffAt (hU.mem_nhds hz)) j
  have j₄ : expJetScalar (fun j => iteratedDeriv j f₃ z) k
      = iteratedDeriv k (fun w => Complex.exp (f₃ w)) z :=
    expJetScalar_iteratedDeriv hU hf₃ hz k
  have hgerm : (fun w => Complex.exp (f₃ w))
      =ᶠ[nhds z] fun w => Complex.exp ((f w - Complex.I) / (f w + Complex.I)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hden : f w + Complex.I ≠ 0 := hne w hw
    congr 1
    simp only [hf₃def, hf₂def, hf₁def, one_mul]
    field_simp
    ring
  rw [← Filter.EventuallyEq.iteratedDeriv_eq k hgerm, ← j₄, chiJetScalar]
  congr 1
  funext j
  rw [j₃]
  congr 1
  funext l
  rw [j₂]
  congr 1
  funext m
  rw [j₁]

/-- Affine jets below a fixed order depend only on the jets below that order. -/
theorem affJetScalar_congr (a b : ℂ) {y y' : ℕ → ℂ} {K : ℕ} (h : ∀ j ≤ K, y j = y' j)
    (k : ℕ) (hk : k ≤ K) : affJetScalar a b y k = affJetScalar a b y' k := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [affJetScalar_apply_zero, affJetScalar_apply_zero, h 0 hk]
  · rw [affJetScalar_apply_of_ne _ _ _ hk0, affJetScalar_apply_of_ne _ _ _ hk0, h k hk]

/-- **The chart is local in the jet order.**  Its `k`-th entry depends only on the jets up to
order `k`. -/
theorem chiJetScalar_congr {y y' : ℕ → ℂ} {K : ℕ} (h : ∀ j ≤ K, y j = y' j) (k : ℕ) (hk : k ≤ K) :
    chiJetScalar y k = chiJetScalar y' k := by
  rw [chiJetScalar, chiJetScalar]
  refine expJetScalar_congr _ _ k fun j hj => ?_
  refine affJetScalar_congr _ _ (K := K) ?_ j (le_trans hj hk)
  intro l hl
  refine invJetScalar_congr (K := K) ?_ l hl
  intro m hm
  exact affJetScalar_congr _ _ h m hm

/-! ## Transport of openness -/

/-- **Openness transports through the chart.**  If a parametrised family of jet packets covers a
neighbourhood of its value, so does the family of Cayley outer jet packets. -/
theorem chiJetScalar_observation_image_mem_nhds {P : Type*} [TopologicalSpace P]
    {J : P → ℕ → ℂ} (hne : ∀ p : P, J p 0 + Complex.I ≠ 0) {p : P} {N : Set P}
    (hJ : J '' N ∈ nhds (J p)) :
    (fun q : P => fun k => chiJetScalar (J q) k) '' N
      ∈ nhds (fun k => chiJetScalar (J p) k) := by
  have h2 := chiJetScalar_image_mem_nhds (hne p) hJ
  rwa [← Set.image_comp] at h2

/-- **Truncation to a finite packet is open.**  Extending a finite packet by the coordinates of the
base point is a continuous right inverse. -/
theorem restrictFin_image_mem_nhds (n : ℕ) (w : ℕ → ℂ) {N : Set (ℕ → ℂ)} (hN : N ∈ nhds w) :
    (fun v : ℕ → ℂ => fun k : Fin (n + 1) => v (k : ℕ)) '' N
      ∈ nhds (fun k : Fin (n + 1) => w (k : ℕ)) := by
  classical
  refine image_mem_nhds_of_continuousAt_rightInverse
    (Φ := fun v : ℕ → ℂ => fun k : Fin (n + 1) => v (k : ℕ))
    (Ψ := fun y : Fin (n + 1) → ℂ => fun j : ℕ => if h : j < n + 1 then y ⟨j, h⟩ else w j)
    hN ?_ ?_ ?_
  · refine Continuous.continuousAt (continuous_pi fun j => ?_)
    by_cases hj : j < n + 1
    · simp only [dif_pos hj]
      exact continuous_apply _
    · simp only [dif_neg hj]
      exact continuous_const
  · funext j
    by_cases hj : j < n + 1
    · simp [hj]
    · simp [hj]
  · intro y
    funext k
    simp [k.isLt]

/-! ## The chart on packets of a fixed order -/

/-- The Cayley outer jet chart on packets of a fixed order. -/
def chiJetPacket (n : ℕ) (y : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  fun k => chiJetScalar (fun j => if h : j < n + 1 then y ⟨j, h⟩ else 0) (k : ℕ)

/-- **The chart on packets carries neighbourhoods to neighbourhoods.**  Locality in the jet order
lets the sequence-level statement descend to a fixed order: truncation is open, and the chart does
not see the discarded coordinates. -/
theorem chiJetPacket_image_mem_nhds {n : ℕ} {y : Fin (n + 1) → ℂ}
    (hy : y 0 + Complex.I ≠ 0) {N : Set (Fin (n + 1) → ℂ)} (hN : N ∈ nhds y) :
    chiJetPacket n '' N ∈ nhds (chiJetPacket n y) := by
  classical
  set ext : (Fin (n + 1) → ℂ) → (ℕ → ℂ) :=
    fun v => fun j => if h : j < n + 1 then v ⟨j, h⟩ else 0 with hext
  set res : (ℕ → ℂ) → (Fin (n + 1) → ℂ) := fun v => fun k => v (k : ℕ) with hres
  have hrescont : Continuous res := continuous_pi fun k => continuous_apply _
  have hresext : res (ext y) = y := by
    funext k
    show (if h : (k : ℕ) < n + 1 then y ⟨(k : ℕ), h⟩ else 0) = y k
    rw [dif_pos k.isLt]
  have hM : res ⁻¹' N ∈ nhds (ext y) := by
    refine hrescont.continuousAt ?_
    rw [hresext]
    exact hN
  have hy' : (ext y) 0 + Complex.I ≠ 0 := by
    simpa [hext] using hy
  have h1 : (fun v : ℕ → ℂ => fun k => chiJetScalar v k) '' (res ⁻¹' N)
      ∈ nhds (fun k => chiJetScalar (ext y) k) := chiJetScalar_image_mem_nhds hy' hM
  have h2 := restrictFin_image_mem_nhds n (fun k => chiJetScalar (ext y) k) h1
  have hbase : (fun k : Fin (n + 1) => chiJetScalar (ext y) (k : ℕ)) = chiJetPacket n y := rfl
  rw [hbase] at h2
  refine Filter.mem_of_superset h2 ?_
  rintro z ⟨w, ⟨v, hv, rfl⟩, rfl⟩
  refine ⟨res v, hv, ?_⟩
  funext k
  refine chiJetScalar_congr (K := n) ?_ (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)
  intro j hj
  show (if h : j < n + 1 then (res v) ⟨j, h⟩ else 0) = v j
  rw [dif_pos (Nat.lt_succ_of_le hj)]

/-! ## Continuity of the chart -/

/-- **The Cayley outer chart is continuous where it is defined.**  Its only singular locus is the
packets whose zeroth jet meets `-i`. -/
theorem continuousOn_chiJetScalar (k : ℕ) :
    ContinuousOn (fun y : ℕ → ℂ => chiJetScalar y k) {y : ℕ → ℂ | y 0 + Complex.I ≠ 0} := by
  set V : Set (ℕ → ℂ) := {y : ℕ → ℂ | y 0 + Complex.I ≠ 0} with hV
  have hA₁cont : Continuous fun y : ℕ → ℂ => fun m => affJetScalar 1 Complex.I y m :=
    continuous_affJetScalar 1 Complex.I
  have hmaps : Set.MapsTo (fun y : ℕ → ℂ => fun m => affJetScalar 1 Complex.I y m) V
      {w : ℕ → ℂ | w 0 ≠ 0} := by
    intro y hy
    show affJetScalar 1 Complex.I y 0 ≠ 0
    rw [affJetScalar_apply_zero, one_mul]
    exact hy
  have hR : ∀ l, ContinuousOn
      (fun y : ℕ → ℂ => invJetScalar (fun m => affJetScalar 1 Complex.I y m) l) V := fun l =>
    (continuousOn_invJetScalar l).comp hA₁cont.continuousOn hmaps
  have hA₂ : ∀ j, ContinuousOn (fun y : ℕ → ℂ =>
      affJetScalar (-(2 * Complex.I)) 1
        (fun l => invJetScalar (fun m => affJetScalar 1 Complex.I y m) l) j) V := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [affJetScalar_apply_zero]
      exact (continuousOn_const.mul (hR 0)).add continuousOn_const
    · simp only [affJetScalar_apply_of_ne _ _ _ hj]
      exact continuousOn_const.mul (hR j)
  simp only [chiJetScalar]
  exact continuousOn_expJetScalar hA₂ k

/-- **The chart on packets is continuous where it is defined.** -/
theorem continuousOn_chiJetPacket (n : ℕ) :
    ContinuousOn (chiJetPacket n) {y : Fin (n + 1) → ℂ | y 0 + Complex.I ≠ 0} := by
  have hext : Continuous fun v : Fin (n + 1) → ℂ =>
      fun j : ℕ => if h : j < n + 1 then v ⟨j, h⟩ else 0 := by
    refine continuous_pi fun j => ?_
    by_cases hj : j < n + 1
    · simp only [dif_pos hj]
      exact continuous_apply _
    · simp only [dif_neg hj]
      exact continuous_const
  have hmaps : Set.MapsTo (fun v : Fin (n + 1) → ℂ =>
      fun j : ℕ => if h : j < n + 1 then v ⟨j, h⟩ else 0)
      {y : Fin (n + 1) → ℂ | y 0 + Complex.I ≠ 0} {w : ℕ → ℂ | w 0 + Complex.I ≠ 0} := by
    intro y hy
    show (if h : (0 : ℕ) < n + 1 then y ⟨0, h⟩ else 0) + Complex.I ≠ 0
    rw [dif_pos (Nat.succ_pos n)]
    exact hy
  rw [continuousOn_pi]
  intro k
  exact (continuousOn_chiJetScalar (k : ℕ)).comp hext.continuousOn hmaps

end

end GaloisForLFunctions.HTGeometry
