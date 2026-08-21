import GaloisForLFunctions.HTGeometry.ConstitutiveLawHistoryHigherDifferential

/-!
# The finite law-history spectral machine

A finite history of linear laws `V 0 → V 1 → ⋯` carries interval transports `A i j`, page
subquotients

* `pageKernel s n = ker aₙ ⊓ range A_{s,n}` — later erasure surviving transport from level `s`;
* `pageCokerSubmodule m t = range aₘ ⊔ ker A_{m+1,t}` — earlier nonattainment surviving erasure
  up to level `t`,

and, for `m + 1 ≤ n`, a canonical page differential from `pageKernel (m+1) n` to
`V (m+1) ⧸ pageCokerSubmodule m n`.  Its kernel is the next kernel survivor and its cokernel is
the next cokernel survivor, so each page is the homology of the previous one.

The stable page reconstructs the total law: the kernel survivors are the graded pieces of the
kernel filtration of `A_{0,m}` and the cokernel survivors are the graded pieces of the image
filtration of its cokernel.  Consequently `A_{0,m}` is bijective exactly when every stable
survivor vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {k : Type u} [Field k] {V : ℕ → Type v}
  [∀ n, AddCommGroup (V n)] [∀ n, Module k (V n)]

/-! ## Interval transports -/

/-- Interval transport `A i j` of a history of linear laws. -/
def transport (a : ∀ n, V n →ₗ[k] V (n + 1)) (i : ℕ) :
    ∀ (j : ℕ), i ≤ j → (V i →ₗ[k] V j)
  | 0, h => cast (congrArg (fun n => V i →ₗ[k] V n) (Nat.le_zero.mp h)) LinearMap.id
  | (j + 1), h =>
      if hij : i = j + 1 then cast (congrArg (fun n => V i →ₗ[k] V n) hij) LinearMap.id
      else (a j).comp (transport a i j (by omega))

@[simp] theorem transport_self (a : ∀ n, V n →ₗ[k] V (n + 1)) (i : ℕ) (h : i ≤ i) :
    transport a i i h = LinearMap.id := by
  cases i with
  | zero => simp [transport]
  | succ n => simp [transport]

@[simp] theorem transport_step (a : ∀ n, V n →ₗ[k] V (n + 1)) {i j : ℕ} (h : i ≤ j) :
    transport a i (j + 1) (h.trans (Nat.le_succ j)) = (a j).comp (transport a i j h) := by
  have hne : i ≠ j + 1 := by omega
  simp [transport, hne]

theorem transport_one (a : ∀ n, V n →ₗ[k] V (n + 1)) (i : ℕ) :
    transport a i (i + 1) (Nat.le_succ i) = a i := by
  rw [transport_step a (le_refl i), transport_self]
  ext x
  simp

/-- Interval transports extend on the left by the incoming law. -/
theorem transport_left (a : ∀ n, V n →ₗ[k] V (n + 1)) {i j : ℕ} (h : i + 1 ≤ j) :
    transport a i j (by omega) = (transport a (i + 1) j h).comp (a i) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hij : i + 1 ≤ j := hlt
      rw [transport_step a (show i ≤ j by omega), transport_step a hij, ih hij,
        LinearMap.comp_assoc]
    · have hji : j = i := by omega
      subst hji
      rw [transport_self, transport_one]
      ext x
      simp

/-- **Strict interval composition.** -/
theorem transport_comp (a : ∀ n, V n →ₗ[k] V (n + 1)) {i j l : ℕ}
    (hij : i ≤ j) (hjl : j ≤ l) :
    (transport a j l hjl).comp (transport a i j hij) = transport a i l (hij.trans hjl) := by
  induction l with
  | zero =>
    have hj : j = 0 := by omega
    subst hj
    rw [transport_self]
    ext x
    simp
  | succ l ih =>
    rcases Nat.lt_or_ge l j with hlt | hge
    · have hj : j = l + 1 := by omega
      subst hj
      rw [transport_self]
      ext x
      simp
    · rw [transport_step a hge, transport_step a (hij.trans hge), LinearMap.comp_assoc,
        ih hge]

/-! ## Page subquotients -/

/-- Later-erasure survivor at level `n` that is already attained from level `s`. -/
abbrev pageKernel (a : ∀ n, V n →ₗ[k] V (n + 1)) (s n : ℕ) (h : s ≤ n) : Submodule k (V n) :=
  higherKernelSource (transport a s n h) (a n)

theorem pageKernel_eq (a : ∀ n, V n →ₗ[k] V (n + 1)) (s n : ℕ) (h : s ≤ n) :
    pageKernel a s n h = LinearMap.ker (a n) ⊓ LinearMap.range (transport a s n h) := rfl

/-- Denominator of the earlier-nonattainment survivor at level `m + 1` that is still not erased
by transport up to level `t`. -/
abbrev pageCokerSubmodule (a : ∀ n, V n →ₗ[k] V (n + 1)) (m t : ℕ) (h : m + 1 ≤ t) :
    Submodule k (V (m + 1)) :=
  secondaryCarrierSubmodule (a m) (transport a (m + 1) t h)

theorem pageCokerSubmodule_eq (a : ∀ n, V n →ₗ[k] V (n + 1)) (m t : ℕ) (h : m + 1 ≤ t) :
    pageCokerSubmodule a m t h
      = LinearMap.range (a m) ⊔ LinearMap.ker (transport a (m + 1) t h) := rfl

/-- **Page one.**  The first kernel survivor is the local kernel. -/
theorem pageKernel_self (a : ∀ n, V n →ₗ[k] V (n + 1)) (n : ℕ) :
    pageKernel a n n (le_refl n) = LinearMap.ker (a n) := by
  rw [pageKernel_eq, transport_self]
  simp

/-- **Page one.**  The first cokernel survivor is the local cokernel. -/
theorem pageCokerSubmodule_self (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    pageCokerSubmodule a m (m + 1) (le_refl (m + 1)) = LinearMap.range (a m) := by
  rw [pageCokerSubmodule_eq, transport_self]
  simp

/-- **The page differential.**  A later-erasure class attained from level `m + 1` is read as an
earlier-nonattainment class at level `m + 1`; the value is independent of the lift. -/
def pageDifferential (a : ∀ n, V n →ₗ[k] V (n + 1)) (m n : ℕ) (h : m + 1 ≤ n) :
    pageKernel a (m + 1) n h →ₗ[k] (V (m + 1) ⧸ pageCokerSubmodule a m n h) :=
  higherLawHistoryDifferential (a m) (transport a (m + 1) n h) (a n)

/-- The next kernel survivor of the machine is the page kernel one level earlier. -/
theorem nextHigherKernelSource_eq_pageKernel (a : ∀ n, V n →ₗ[k] V (n + 1))
    (m n : ℕ) (h : m + 1 ≤ n) :
    nextHigherKernelSource (a m) (transport a (m + 1) n h) (a n)
      = pageKernel a m n (by omega) := by
  show LinearMap.ker (a n) ⊓ LinearMap.range ((transport a (m + 1) n h).comp (a m))
    = LinearMap.ker (a n) ⊓ LinearMap.range (transport a m n (by omega))
  rw [← transport_left a h]

/-- The next cokernel denominator of the machine is the page cokernel one level later. -/
theorem secondaryCarrierSubmodule_eq_pageCokerSubmodule (a : ∀ n, V n →ₗ[k] V (n + 1))
    (m n : ℕ) (h : m + 1 ≤ n) :
    secondaryCarrierSubmodule (a m) ((a n).comp (transport a (m + 1) n h))
      = pageCokerSubmodule a m (n + 1) (by omega) := by
  show LinearMap.range (a m) ⊔ LinearMap.ker ((a n).comp (transport a (m + 1) n h))
    = LinearMap.range (a m) ⊔ LinearMap.ker (transport a (m + 1) (n + 1) (by omega))
  rw [← transport_step a h]

/-- **Exact page derivation, kernel half.**  The kernel of the page differential is the next
kernel survivor. -/
theorem ker_pageDifferential (a : ∀ n, V n →ₗ[k] V (n + 1)) (m n : ℕ) (h : m + 1 ≤ n) :
    LinearMap.ker (pageDifferential a m n h)
      = Submodule.comap (pageKernel a (m + 1) n h).subtype (pageKernel a m n (by omega)) := by
  rw [pageDifferential, ← range_nextHigherKernelInclusion_eq_ker]
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    have hw : (w : V n) ∈ pageKernel a m n (by omega) := by
      rw [← nextHigherKernelSource_eq_pageKernel a m n h]
      exact w.2
    exact hw
  · intro hz
    have hz' : (z : V n) ∈ nextHigherKernelSource (a m) (transport a (m + 1) n h) (a n) := by
      rw [nextHigherKernelSource_eq_pageKernel a m n h]
      exact hz
    exact ⟨⟨z.1, hz'⟩, Subtype.ext rfl⟩

/-- **Exact page derivation, cokernel half.**  The cokernel of the page differential is the next
cokernel survivor. -/
def cokerPageDifferentialEquiv (a : ∀ n, V n →ₗ[k] V (n + 1)) (m n : ℕ) (h : m + 1 ≤ n) :
    ((V (m + 1) ⧸ pageCokerSubmodule a m n h) ⧸
        LinearMap.range (pageDifferential a m n h))
      ≃ₗ[k] (V (m + 1) ⧸ pageCokerSubmodule a m (n + 1) (by omega)) :=
  (higherDifferentialCokerEquivNext (a m) (transport a (m + 1) n h) (a n)).trans
    (Submodule.quotEquivOfEq _ _
      (secondaryCarrierSubmodule_eq_pageCokerSubmodule a m n h))

/-! ## Subquotients -/

section Subquotient

variable {Y : Type*} [AddCommGroup Y] [Module k Y]

/-- A subquotient of nested submodules is the image of the larger one in the quotient by the
smaller one. -/
def subquotientEquivMapMkQ (M N : Submodule k Y) :
    (M ⧸ Submodule.comap M.subtype N) ≃ₗ[k] Submodule.map N.mkQ M :=
  have hker : LinearMap.ker (N.mkQ.comp M.subtype) = Submodule.comap M.subtype N := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (N.mkQ.comp M.subtype) = Submodule.map N.mkQ M := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  (Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((N.mkQ.comp M.subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

end Subquotient

/-! ## The stable kernel filtration -/

/-- The transport of the whole history up to level `m`. -/
abbrev totalTransport (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) : V 0 →ₗ[k] V m :=
  transport a 0 m (Nat.zero_le m)

/-- The canonical filtration of the total kernel by the length of survival. -/
abbrev totalKernelFiltration (a : ∀ n, V n →ₗ[k] V (n + 1)) (j : ℕ) : Submodule k (V 0) :=
  LinearMap.ker (totalTransport a j)

theorem totalKernelFiltration_zero (a : ∀ n, V n →ₗ[k] V (n + 1)) :
    totalKernelFiltration a 0 = ⊥ := by
  rw [totalKernelFiltration, totalTransport, transport_self]
  exact LinearMap.ker_id

theorem totalKernelFiltration_mono (a : ∀ n, V n →ₗ[k] V (n + 1)) (j : ℕ) :
    totalKernelFiltration a j ≤ totalKernelFiltration a (j + 1) := by
  intro x hx
  have : totalTransport a (j + 1) = (a j).comp (totalTransport a j) :=
    transport_step a (Nat.zero_le j)
  rw [LinearMap.mem_ker, this, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

/-- The graded piece of the kernel filtration is the stable kernel survivor. -/
theorem map_totalTransport_totalKernelFiltration (a : ∀ n, V n →ₗ[k] V (n + 1)) (j : ℕ) :
    Submodule.map (totalTransport a j) (totalKernelFiltration a (j + 1))
      = pageKernel a 0 j (Nat.zero_le j) := by
  have hstep : totalTransport a (j + 1) = (a j).comp (totalTransport a j) :=
    transport_step a (Nat.zero_le j)
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨?_, ⟨x, rfl⟩⟩
    have hx0 := LinearMap.mem_ker.mp hx
    rw [hstep, LinearMap.comp_apply] at hx0
    exact hx0
  · rintro y ⟨hy, x, rfl⟩
    refine ⟨x, ?_, rfl⟩
    show x ∈ LinearMap.ker (totalTransport a (j + 1))
    rw [LinearMap.mem_ker, hstep, LinearMap.comp_apply]
    exact hy

/-- **Kernel reconstruction (LHS.17).**  The graded pieces of the survival filtration of the total
kernel are exactly the stable kernel survivors. -/
def kernelGradedEquiv (a : ∀ n, V n →ₗ[k] V (n + 1)) (j : ℕ) :
    (totalKernelFiltration a (j + 1) ⧸
        Submodule.comap (totalKernelFiltration a (j + 1)).subtype (totalKernelFiltration a j))
      ≃ₗ[k] pageKernel a 0 j (Nat.zero_le j) :=
  have hker : LinearMap.ker ((totalTransport a j).domRestrict (totalKernelFiltration a (j + 1)))
      = Submodule.comap (totalKernelFiltration a (j + 1)).subtype (totalKernelFiltration a j) := by
    rw [LinearMap.domRestrict, LinearMap.ker_comp]
  have hrange :
      LinearMap.range ((totalTransport a j).domRestrict (totalKernelFiltration a (j + 1)))
        = pageKernel a 0 j (Nat.zero_le j) := by
    rw [LinearMap.domRestrict, LinearMap.range_comp, Submodule.range_subtype]
    exact map_totalTransport_totalKernelFiltration a j
  (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (((totalTransport a j).domRestrict (totalKernelFiltration a (j + 1))).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ hrange))

/-! ## The stable cokernel filtration -/

/-- The total cokernel of a history of length `m`. -/
abbrev totalCokernel (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) : Type v :=
  V m ⧸ LinearMap.range (totalTransport a m)

/-- The filtration of the total cokernel by future-tail images. -/
abbrev totalCokerFiltration (a : ∀ n, V n →ₗ[k] V (n + 1)) (m i : ℕ) (h : i ≤ m) :
    Submodule k (totalCokernel a m) :=
  Submodule.map (LinearMap.range (totalTransport a m)).mkQ (LinearMap.range (transport a i m h))

theorem range_totalTransport_le (a : ∀ n, V n →ₗ[k] V (n + 1)) {i m : ℕ} (h : i ≤ m) :
    LinearMap.range (totalTransport a m) ≤ LinearMap.range (transport a i m h) := by
  rintro y ⟨x, rfl⟩
  exact ⟨transport a 0 i (Nat.zero_le i) x, by
    rw [← LinearMap.comp_apply, transport_comp a (Nat.zero_le i) h]⟩

theorem totalCokerFiltration_zero (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    totalCokerFiltration a m 0 (Nat.zero_le m) = ⊥ := by
  rw [eq_bot_iff]
  rintro q ⟨y, hy, rfl⟩
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hy

theorem totalCokerFiltration_top (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    totalCokerFiltration a m m (le_refl m) = ⊤ := by
  rw [totalCokerFiltration, transport_self, LinearMap.range_id, Submodule.map_top,
    Submodule.range_mkQ]

theorem totalCokerFiltration_mono (a : ∀ n, V n →ₗ[k] V (n + 1)) {m i : ℕ} (h : i + 1 ≤ m) :
    totalCokerFiltration a m i (by omega) ≤ totalCokerFiltration a m (i + 1) h := by
  refine Submodule.map_mono ?_
  rw [transport_left a h]
  exact LinearMap.range_comp_le_range _ _

/-- The map that computes the graded piece of the cokernel filtration. -/
def cokerGradedMap (a : ∀ n, V n →ₗ[k] V (n + 1)) (m m' : ℕ) (h : m' + 1 ≤ m) :
    V (m' + 1) →ₗ[k] (totalCokernel a m ⧸ totalCokerFiltration a m m' (by omega)) :=
  ((totalCokerFiltration a m m' (by omega)).mkQ).comp
    (((LinearMap.range (totalTransport a m)).mkQ).comp (transport a (m' + 1) m h))

theorem range_cokerGradedMap (a : ∀ n, V n →ₗ[k] V (n + 1)) (m m' : ℕ) (h : m' + 1 ≤ m) :
    LinearMap.range (cokerGradedMap a m m' h)
      = Submodule.map (totalCokerFiltration a m m' (by omega)).mkQ
          (totalCokerFiltration a m (m' + 1) h) := by
  rw [cokerGradedMap, LinearMap.range_comp, LinearMap.range_comp]

theorem ker_cokerGradedMap (a : ∀ n, V n →ₗ[k] V (n + 1)) (m m' : ℕ) (h : m' + 1 ≤ m) :
    LinearMap.ker (cokerGradedMap a m m' h) = pageCokerSubmodule a m' m h := by
  apply le_antisymm
  · intro y hy
    have hy0 : (totalCokerFiltration a m m' (by omega)).mkQ
        ((LinearMap.range (totalTransport a m)).mkQ (transport a (m' + 1) m h y)) = 0 := hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy0
    obtain ⟨u, hu, hmk⟩ := hy0
    have hdiff : transport a (m' + 1) m h y - u ∈ LinearMap.range (totalTransport a m) :=
      (Submodule.Quotient.eq _).mp hmk.symm
    have hmem : transport a (m' + 1) m h y ∈ LinearMap.range (transport a m' m (by omega)) := by
      have h1 : transport a (m' + 1) m h y
          = (transport a (m' + 1) m h y - u) + u := by abel
      rw [h1]
      exact Submodule.add_mem _ (range_totalTransport_le a (by omega) hdiff) hu
    obtain ⟨x, hx⟩ := hmem
    have hax : transport a (m' + 1) m h (a m' x) = transport a (m' + 1) m h y := by
      rw [← LinearMap.comp_apply, ← transport_left a h]
      exact hx
    refine Submodule.mem_sup.mpr ⟨a m' x, ⟨x, rfl⟩, y - a m' x, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hax, sub_self]
  · refine sup_le ?_ ?_
    · rintro y ⟨x, rfl⟩
      have hax : transport a (m' + 1) m h (a m' x) = transport a m' m (by omega) x := by
        rw [← LinearMap.comp_apply, ← transport_left a h]
      show (totalCokerFiltration a m m' (by omega)).mkQ
        ((LinearMap.range (totalTransport a m)).mkQ (transport a (m' + 1) m h (a m' x))) = 0
      rw [hax, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨transport a m' m (by omega) x, ⟨x, rfl⟩, rfl⟩
    · intro y hy
      show (totalCokerFiltration a m m' (by omega)).mkQ
        ((LinearMap.range (totalTransport a m)).mkQ (transport a (m' + 1) m h y)) = 0
      rw [LinearMap.mem_ker] at hy
      rw [hy, map_zero, map_zero]

/-- **Cokernel reconstruction (LHS.20).**  The graded pieces of the future-tail filtration of the
total cokernel are exactly the stable cokernel survivors. -/
def cokerGradedEquiv (a : ∀ n, V n →ₗ[k] V (n + 1)) (m m' : ℕ) (h : m' + 1 ≤ m) :
    (V (m' + 1) ⧸ pageCokerSubmodule a m' m h)
      ≃ₗ[k] Submodule.map (totalCokerFiltration a m m' (by omega)).mkQ
          (totalCokerFiltration a m (m' + 1) h) :=
  (Submodule.quotEquivOfEq _ _ (ker_cokerGradedMap a m m' h).symm).trans
    ((cokerGradedMap a m m' h).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (range_cokerGradedMap a m m' h)))

/-- The same statement in subquotient form. -/
def cokerGradedSubquotientEquiv (a : ∀ n, V n →ₗ[k] V (n + 1)) (m m' : ℕ) (h : m' + 1 ≤ m) :
    (totalCokerFiltration a m (m' + 1) h ⧸
        Submodule.comap (totalCokerFiltration a m (m' + 1) h).subtype
          (totalCokerFiltration a m m' (by omega)))
      ≃ₗ[k] (V (m' + 1) ⧸ pageCokerSubmodule a m' m h) :=
  (subquotientEquivMapMkQ _ _).trans (cokerGradedEquiv a m m' h).symm

/-! ## Three-law fusion -/

section ThreeLaw

variable {X Y Z W : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z] [AddCommGroup W] [Module k W]

/-- The kernel of a higher transgression is the next kernel survivor, read inside the current
one. -/
theorem ker_higherLawHistoryDifferential (a : X →ₗ[k] Y) (p : Y →ₗ[k] Z) (q : Z →ₗ[k] W) :
    LinearMap.ker (higherLawHistoryDifferential a p q)
      = Submodule.comap (higherKernelSource p q).subtype (nextHigherKernelSource a p q) := by
  rw [← range_nextHigherKernelInclusion_eq_ker]
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    exact w.2
  · intro z hz
    exact ⟨⟨z.1, hz⟩, Subtype.ext rfl⟩

/-- **(LHS.22).**  For three laws, the kernel of the page-two differential consists of the classes
erased by the last law that are already attained by the composite of the first two. -/
theorem ker_pageTwoDifferential (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) (h : Z →ₗ[k] W) :
    LinearMap.ker (higherLawHistoryDifferential f g h)
      = Submodule.comap (higherKernelSource g h).subtype
          (LinearMap.ker h ⊓ LinearMap.range (g.comp f)) :=
  ker_higherLawHistoryDifferential f g h

/-- **(LHS.23).**  For three laws, the cokernel of the page-two differential is the earlier
carrier modulo the first range together with the kernel of the last two laws. -/
def pageTwoCokerEquiv (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) (h : Z →ₗ[k] W) :
    ((Y ⧸ (LinearMap.range f ⊔ LinearMap.ker g)) ⧸
        LinearMap.range (higherLawHistoryDifferential f g h))
      ≃ₗ[k] (Y ⧸ (LinearMap.range f ⊔ LinearMap.ker (h.comp g))) :=
  higherDifferentialCokerEquivNext f g h

end ThreeLaw

/-! ## Composite rigidity -/

theorem pageKernel_mono (a : ∀ n, V n →ₗ[k] V (n + 1)) {m n : ℕ} (h : m + 1 ≤ n) :
    pageKernel a m n (by omega) ≤ pageKernel a (m + 1) n h := by
  refine inf_le_inf_left _ ?_
  rw [transport_left a h]
  exact LinearMap.range_comp_le_range _ _

theorem totalKernelFiltration_eq_bot_iff (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    totalKernelFiltration a m = ⊥ ↔ ∀ j < m, pageKernel a 0 j (Nat.zero_le j) = ⊥ := by
  induction m with
  | zero =>
    simp [totalKernelFiltration_zero]
  | succ m ih =>
    constructor
    · intro hm j hj
      have hmm : totalKernelFiltration a m = ⊥ :=
        le_bot_iff.mp (hm ▸ totalKernelFiltration_mono a m)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact ih.mp hmm j hlt
      · subst heq
        rw [← map_totalTransport_totalKernelFiltration a j, hm, Submodule.map_bot]
    · intro hall
      have hmm : totalKernelFiltration a m = ⊥ := ih.mpr fun j hj => hall j (by omega)
      have hgr : Submodule.map (totalTransport a m) (totalKernelFiltration a (m + 1)) = ⊥ := by
        rw [map_totalTransport_totalKernelFiltration]
        exact hall m (by omega)
      have hle : totalKernelFiltration a (m + 1) ≤ totalKernelFiltration a m := by
        intro x hx
        have hmem : totalTransport a m x
            ∈ Submodule.map (totalTransport a m) (totalKernelFiltration a (m + 1)) :=
          ⟨x, hx, rfl⟩
        rw [hgr, Submodule.mem_bot] at hmem
        exact hmem
      exact le_bot_iff.mp (hle.trans hmm.le)

theorem totalCokerFiltration_eq_bot_iff (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    ∀ (i : ℕ) (h : i ≤ m),
      totalCokerFiltration a m i h = ⊥ ↔
        ∀ (m' : ℕ) (h' : m' + 1 ≤ m), m' < i → pageCokerSubmodule a m' m h' = ⊤ := by
  intro i
  induction i with
  | zero =>
    intro h
    exact ⟨fun _ m' _ hm' => absurd hm' (Nat.not_lt_zero m'),
      fun _ => totalCokerFiltration_zero a m⟩
  | succ i ih =>
    intro h
    have him : i ≤ m := by omega
    have hmono : totalCokerFiltration a m i him ≤ totalCokerFiltration a m (i + 1) h :=
      totalCokerFiltration_mono a h
    have hgr : Submodule.map (totalCokerFiltration a m i him).mkQ
        (totalCokerFiltration a m (i + 1) h) = ⊥ ↔ pageCokerSubmodule a i m h = ⊤ := by
      rw [← range_cokerGradedMap a m i h, LinearMap.range_eq_bot, ← LinearMap.ker_eq_top,
        ker_cokerGradedMap]
    constructor
    · intro hbot m' h' hm'
      have hib : totalCokerFiltration a m i him = ⊥ :=
        le_bot_iff.mp (hbot ▸ hmono)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hlt | heq
      · exact (ih him).mp hib m' h' hlt
      · subst heq
        refine hgr.mp ?_
        rw [hbot, Submodule.map_bot]
    · intro hall
      have hib : totalCokerFiltration a m i him = ⊥ :=
        (ih him).mpr fun m' h' hm' => hall m' h' (Nat.lt_succ_of_lt hm')
      have hb : Submodule.map (totalCokerFiltration a m i him).mkQ
          (totalCokerFiltration a m (i + 1) h) = ⊥ :=
        hgr.mpr (hall i h (Nat.lt_succ_self i))
      have hle : totalCokerFiltration a m (i + 1) h ≤ totalCokerFiltration a m i him := by
        intro q hq
        have hmem : (totalCokerFiltration a m i him).mkQ q
            ∈ Submodule.map (totalCokerFiltration a m i him).mkQ
              (totalCokerFiltration a m (i + 1) h) := ⟨q, hq, rfl⟩
        rw [hb, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
        exact hmem
      exact le_bot_iff.mp (hle.trans hib.le)

/-- **Composite rigidity (LHS.25).**  The total law of a finite history is bijective exactly when
every stable kernel survivor vanishes and every stable cokernel survivor vanishes. -/
theorem totalTransport_bijective_iff (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    Function.Bijective (totalTransport a m)
      ↔ (∀ j < m, pageKernel a 0 j (Nat.zero_le j) = ⊥)
        ∧ (∀ (m' : ℕ) (h : m' + 1 ≤ m), pageCokerSubmodule a m' m h = ⊤) := by
  have hsurj : Function.Surjective (totalTransport a m)
      ↔ ∀ (m' : ℕ) (h : m' + 1 ≤ m), pageCokerSubmodule a m' m h = ⊤ := by
    have hkey : totalCokerFiltration a m m (le_refl m) = ⊥ ↔
        ∀ (m' : ℕ) (h : m' + 1 ≤ m), m' < m → pageCokerSubmodule a m' m h = ⊤ :=
      totalCokerFiltration_eq_bot_iff a m m (le_refl m)
    rw [totalCokerFiltration_top] at hkey
    constructor
    · intro hs m' h'
      refine hkey.mp ?_ m' h' (by omega)
      rw [eq_bot_iff]
      intro q _
      induction q using Submodule.Quotient.induction_on with | _ y => ?_
      obtain ⟨x, hx⟩ := hs y
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, hx⟩
    · intro hall
      have htop : (⊤ : Submodule k (totalCokernel a m)) = ⊥ :=
        hkey.mpr fun m' h' _ => hall m' h'
      intro y
      have hy : (Submodule.Quotient.mk y : totalCokernel a m) = 0 := by
        have : (Submodule.Quotient.mk y : totalCokernel a m) ∈ (⊥ : Submodule k _) := by
          rw [← htop]; trivial
        exact (Submodule.mem_bot _).mp this
      rw [Submodule.Quotient.mk_eq_zero] at hy
      exact hy
  rw [Function.Bijective, ← LinearMap.ker_eq_bot, hsurj,
    totalKernelFiltration_eq_bot_iff a m]

/-! ## Finite index conservation -/

section FiniteDim

variable [∀ n, FiniteDimensional k (V n)]

/-- The index of the total law is the sum of the local indices. -/
theorem finiteLawIndex_totalTransport (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    finiteLawIndex (totalTransport a m) = ∑ j ∈ Finset.range m, finiteLawIndex (a j) := by
  induction m with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, totalTransport, transport_self,
      finiteLawIndex_eq_finrank_sub]
    omega
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, totalTransport, transport_step a (Nat.zero_le m),
      finiteLawIndex_comp]

/-- **Pagewise index conservation (LHS.24).**  Passing to the next page preserves the signed
difference of kernel and cokernel dimensions. -/
theorem pagewise_index_conservation (a : ∀ n, V n →ₗ[k] V (n + 1)) {m n : ℕ} (h : m + 1 ≤ n) :
    (Module.finrank k (pageKernel a m n (by omega)) : ℤ)
        - Module.finrank k (V (m + 1) ⧸ pageCokerSubmodule a m (n + 1) (by omega))
      = (Module.finrank k (pageKernel a (m + 1) n h) : ℤ)
        - Module.finrank k (V (m + 1) ⧸ pageCokerSubmodule a m n h) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (pageDifferential a m n h)
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (pageDifferential a m n h))
  have hker : Module.finrank k (LinearMap.ker (pageDifferential a m n h))
      = Module.finrank k (pageKernel a m n (by omega)) := by
    rw [ker_pageDifferential]
    exact (Submodule.comapSubtypeEquivOfLe (pageKernel_mono a h)).finrank_eq
  have hcok : Module.finrank k
      ((V (m + 1) ⧸ pageCokerSubmodule a m n h) ⧸
        LinearMap.range (pageDifferential a m n h))
      = Module.finrank k (V (m + 1) ⧸ pageCokerSubmodule a m (n + 1) (by omega)) :=
    (cokerPageDifferentialEquiv a m n h).finrank_eq
  omega

/-- Dimension of the stable cokernel survivor at level `m' + 1`, zero past the end. -/
def stableCokerRank (a : ∀ n, V n →ₗ[k] V (n + 1)) (m m' : ℕ) : ℕ :=
  if h : m' + 1 ≤ m then Module.finrank k (V (m' + 1) ⧸ pageCokerSubmodule a m' m h) else 0

omit [∀ (n : ℕ), FiniteDimensional k (V n)] in
theorem stableCokerRank_of_le (a : ∀ n, V n →ₗ[k] V (n + 1)) {m m' : ℕ} (h : m' + 1 ≤ m) :
    stableCokerRank a m m' = Module.finrank k (V (m' + 1) ⧸ pageCokerSubmodule a m' m h) := by
  rw [stableCokerRank, dif_pos h]

/-- **Stable kernel sum (LHS.21).**  The total kernel dimension is the sum of the stable kernel
survivor dimensions. -/
theorem sum_finrank_pageKernel (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    ∑ j ∈ Finset.range m, Module.finrank k (pageKernel a 0 j (Nat.zero_le j))
      = Module.finrank k (LinearMap.ker (totalTransport a m)) := by
  induction m with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, totalTransport, transport_self, LinearMap.ker_id,
      finrank_bot]
  | succ m ih =>
    have hsub := Submodule.finrank_quotient_add_finrank
      (Submodule.comap (totalKernelFiltration a (m + 1)).subtype (totalKernelFiltration a m))
    have hlow : Module.finrank k
        (Submodule.comap (totalKernelFiltration a (m + 1)).subtype
          (totalKernelFiltration a m))
        = Module.finrank k (totalKernelFiltration a m) :=
      (Submodule.comapSubtypeEquivOfLe (totalKernelFiltration_mono a m)).finrank_eq
    have hgr : Module.finrank k
        (totalKernelFiltration a (m + 1) ⧸
          Submodule.comap (totalKernelFiltration a (m + 1)).subtype
            (totalKernelFiltration a m))
        = Module.finrank k (pageKernel a 0 m (Nat.zero_le m)) :=
      (kernelGradedEquiv a m).finrank_eq
    have hb1 : Module.finrank k (LinearMap.ker (totalTransport a m))
        = Module.finrank k (totalKernelFiltration a m) := rfl
    have hb2 : Module.finrank k (LinearMap.ker (totalTransport a (m + 1)))
        = Module.finrank k (totalKernelFiltration a (m + 1)) := rfl
    rw [Finset.sum_range_succ, ih]
    omega

theorem finrank_totalCokerFiltration (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    ∀ (i : ℕ) (h : i ≤ m),
      Module.finrank k (totalCokerFiltration a m i h)
        = ∑ j ∈ Finset.range i, stableCokerRank a m j := by
  intro i
  induction i with
  | zero =>
    intro h
    rw [Finset.range_zero, Finset.sum_empty, totalCokerFiltration_zero, finrank_bot]
  | succ i ih =>
    intro h
    have him : i ≤ m := by omega
    have hsub := Submodule.finrank_quotient_add_finrank
      (Submodule.comap (totalCokerFiltration a m (i + 1) h).subtype
        (totalCokerFiltration a m i him))
    have hlow : Module.finrank k
        (Submodule.comap (totalCokerFiltration a m (i + 1) h).subtype
          (totalCokerFiltration a m i him))
        = Module.finrank k (totalCokerFiltration a m i him) :=
      (Submodule.comapSubtypeEquivOfLe (totalCokerFiltration_mono a h)).finrank_eq
    have hgr : Module.finrank k
        (totalCokerFiltration a m (i + 1) h ⧸
          Submodule.comap (totalCokerFiltration a m (i + 1) h).subtype
            (totalCokerFiltration a m i him))
        = stableCokerRank a m i := by
      rw [stableCokerRank_of_le a h]
      exact (cokerGradedSubquotientEquiv a m i h).finrank_eq
    rw [Finset.sum_range_succ, ← ih him]
    omega

/-- **Stable cokernel sum (LHS.21).**  The total cokernel dimension is the sum of the stable
cokernel survivor dimensions. -/
theorem sum_stableCokerRank (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    ∑ j ∈ Finset.range m, stableCokerRank a m j
      = Module.finrank k (V m ⧸ LinearMap.range (totalTransport a m)) := by
  rw [← finrank_totalCokerFiltration a m m (le_refl m), totalCokerFiltration_top, finrank_top]

/-- **Stable-page index conservation (LHS.24).**  The signed sum over the stable page equals the
signed sum over page one, namely the index of the total law. -/
theorem stable_page_index_eq (a : ∀ n, V n →ₗ[k] V (n + 1)) (m : ℕ) :
    ((∑ j ∈ Finset.range m, Module.finrank k (pageKernel a 0 j (Nat.zero_le j)) : ℕ) : ℤ)
        - ((∑ j ∈ Finset.range m, stableCokerRank a m j : ℕ) : ℤ)
      = ∑ j ∈ Finset.range m, finiteLawIndex (a j) := by
  rw [sum_finrank_pageKernel, sum_stableCokerRank, ← finiteLawIndex_totalTransport,
    finiteLawIndex]

end FiniteDim

end

end GaloisForLFunctions.HTGeometry
