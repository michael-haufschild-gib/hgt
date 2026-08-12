import Mathlib
import GaloisForLFunctions.RHTower.RouteEForbiddenSupportStability

/-!
# Polarized incidence and the capacity-phase separation

On a finite signed multigraph whose every edge runs from a positive to a negative vertex, the
diagonal Möbius polarization `S_ε` turns the signless endpoint incidence `B⁺` into the ordinary
oriented boundary `∂`.  Polarization is diagonal with unimodular entries, so it changes no vertex
label, no support, no absolute coordinate norm, and nothing at all on edges — in particular no edge
capacity and no absolute edge-work functional.

Consequently the capacity residual `r = w - B⁺q` obeys a polarized discrete Stokes law
`S_ε w = ∂q + S_ε r`, whose piAugmentation and cut-pairing forms say that the polarized source charge
is a signed cut flux plus an unmatched residual.  On a connected graph the degree-zero quotient is
one dimensional and the polarized class is exactly the signed total capacity.

The finite ordered-prime path realizes the same boundary type through the exact Abel decomposition
`z_N = ∂q_N + b_N`.  But the two capacity geometries are not the same: the Abel prefix primitive
`T_{n+1}` is unbounded relative to the natural local edge capacity `t_{n+1}`, and the associated
log-gap work diverges.  So a common polarized degree-zero boundary type does not imply a common
capacity-filtered boundary phase.
-/

noncomputable section

namespace HTGeometry.ConstraintRelativity

open Finset

/-! ## Polarized signless incidence -/

section Incidence

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (s t : E → V) (eps : V → ℂ)

/-- **Card `(1)`.**  Signless endpoint incidence. -/
def signlessIncidence : (E → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun q := fun v => ∑ e : E, q e * ((if s e = v then 1 else 0) + (if t e = v then 1 else 0))
  map_add' q p := by
    funext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  map_smul' c q := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring

/-- **Card `(1)`.**  Oriented boundary. -/
def orientedBoundary : (E → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun q := fun v => ∑ e : E, q e * ((if s e = v then 1 else 0) - (if t e = v then 1 else 0))
  map_add' q p := by
    funext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  map_smul' c q := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring

/-- **Card `(1)`.**  Möbius polarization. -/
def polarization : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun w := fun v => eps v * w v
  map_add' w u := by
    funext v
    simp only [Pi.add_apply]
    ring
  map_smul' c w := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype V] [DecidableEq E] in
@[simp] theorem signlessIncidence_apply (q : E → ℂ) (v : V) :
    signlessIncidence s t q v =
      ∑ e : E, q e * ((if s e = v then 1 else 0) + (if t e = v then 1 else 0)) := rfl

omit [Fintype V] [DecidableEq E] in
@[simp] theorem orientedBoundary_apply (q : E → ℂ) (v : V) :
    orientedBoundary s t q v =
      ∑ e : E, q e * ((if s e = v then 1 else 0) - (if t e = v then 1 else 0)) := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem polarization_apply (w : V → ℂ) (v : V) :
    polarization eps w v = eps v * w v := rfl

omit [Fintype V] [DecidableEq E] in
/-- **Theorem A, card `(2)` boxed.**  Möbius polarization identifies signless endpoint incidence
with the ordinary oriented boundary. -/
theorem polarization_comp_signlessIncidence
    (hs : ∀ e : E, eps (s e) = 1) (ht : ∀ e : E, eps (t e) = -1) :
    (polarization eps).comp (signlessIncidence s t) = orientedBoundary s t := by
  apply LinearMap.ext
  intro q
  funext v
  rw [LinearMap.comp_apply, polarization_apply, signlessIncidence_apply, orientedBoundary_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : s e = v
  · have hv : eps v = 1 := by rw [← h1]; exact hs e
    have h2 : t e ≠ v := by
      intro h2
      have := ht e
      rw [h2, hv] at this
      norm_num at this
    rw [if_pos h1, if_neg h2, hv]
    ring
  · by_cases h2 : t e = v
    · have hv : eps v = -1 := by rw [← h2]; exact ht e
      rw [if_neg h1, if_pos h2, hv]
      ring
    · rw [if_neg h1, if_neg h2]
      ring

omit [Fintype V] [DecidableEq V] in
/-- Polarization is unimodular, so it preserves every absolute vertex coordinate. -/
theorem norm_polarization_apply (hmod : ∀ v : V, ‖eps v‖ = 1) (w : V → ℂ) (v : V) :
    ‖polarization eps w v‖ = ‖w v‖ := by
  rw [polarization_apply, norm_mul, hmod, one_mul]

omit [Fintype V] [DecidableEq V] in
/-- **Theorem A, port identity.**  Polarization commutes with restriction to a marked port set. -/
theorem polarization_restrict (A : Set V) (w : V → ℂ) (v : A) :
    (polarization eps w) (v : V) = polarization (fun u : A => eps (u : V)) (fun u : A => w u) v :=
  rfl

/-! ## The polarized discrete Stokes law -/

/-- **Card `(4)`.**  The algebraic capacity residual. -/
def capacityResidual (w : V → ℂ) (q : E → ℂ) : V → ℂ :=
  w - signlessIncidence s t q

omit [Fintype V] [DecidableEq E] in
/-- **Theorem B, card `(5)` boxed.**  The polarized discrete Stokes law. -/
theorem polarized_stokes (hs : ∀ e : E, eps (s e) = 1) (ht : ∀ e : E, eps (t e) = -1)
    (w : V → ℂ) (q : E → ℂ) :
    polarization eps w =
      orientedBoundary s t q + polarization eps (capacityResidual s t w q) := by
  funext v
  have hA := congrArg (fun F => F q v) (polarization_comp_signlessIncidence s t eps hs ht)
  simp only [LinearMap.comp_apply, polarization_apply] at hA
  simp only [Pi.add_apply, polarization_apply, capacityResidual, Pi.sub_apply]
  rw [← hA]
  ring

omit [DecidableEq E] in
/-- Augmentation kills oriented boundaries. -/
theorem sum_orientedBoundary (q : E → ℂ) : ∑ v : V, orientedBoundary s t q v = 0 := by
  have hval : ∀ v : V, orientedBoundary s t q v =
      ∑ e : E, q e * ((if s e = v then 1 else 0) - (if t e = v then 1 else 0)) := fun _ => rfl
  rw [Finset.sum_congr rfl (fun v _ => hval v), Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hexp : ∀ v : V, q e * ((if s e = v then 1 else 0) - (if t e = v then 1 else 0))
      = (if s e = v then q e else 0) - (if t e = v then q e else 0) := by
    intro v
    by_cases h1 : s e = v <;> by_cases h2 : t e = v <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun v _ => hexp v), Finset.sum_sub_distrib,
    Finset.sum_ite_eq Finset.univ (s e) (fun _ => q e),
    Finset.sum_ite_eq Finset.univ (t e) (fun _ => q e),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), sub_self]

omit [DecidableEq E] in
/-- Pairing an oriented boundary with a cut cochain is the signed cut flux. -/
theorem sum_orientedBoundary_mul (q : E → ℂ) (chi : V → ℂ) :
    ∑ v : V, orientedBoundary s t q v * chi v =
      ∑ e : E, q e * (chi (s e) - chi (t e)) := by
  have hval : ∀ v : V, orientedBoundary s t q v * chi v =
      ∑ e : E, q e * ((if s e = v then 1 else 0) - (if t e = v then 1 else 0)) * chi v := by
    intro v
    rw [orientedBoundary_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun v _ => hval v), Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hexp : ∀ v : V,
      q e * ((if s e = v then 1 else 0) - (if t e = v then 1 else 0)) * chi v
      = (if s e = v then q e * chi v else 0) - (if t e = v then q e * chi v else 0) := by
    intro v
    by_cases h1 : s e = v <;> by_cases h2 : t e = v <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun v _ => hexp v), Finset.sum_sub_distrib,
    Finset.sum_ite_eq Finset.univ (s e) (fun v => q e * chi v),
    Finset.sum_ite_eq Finset.univ (t e) (fun v => q e * chi v),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  ring

omit [DecidableEq E] in
/-- **Theorem B, card `(6)`.**  The polarized source charge equals the polarized residual charge. -/
theorem polarized_charge (hs : ∀ e : E, eps (s e) = 1) (ht : ∀ e : E, eps (t e) = -1)
    (w : V → ℂ) (q : E → ℂ) :
    ∑ v : V, eps v * w v = ∑ v : V, eps v * capacityResidual s t w q v := by
  have hstokes := polarized_stokes s t eps hs ht w q
  have hsum := congrArg (fun F : V → ℂ => ∑ v : V, F v) hstokes
  simp only [Pi.add_apply, polarization_apply] at hsum
  rw [Finset.sum_add_distrib, sum_orientedBoundary, zero_add] at hsum
  exact hsum

omit [DecidableEq E] in
/-- **Theorem B, card `(7)` boxed.**  The polarized cut-pairing law: polarized source charge is
signed cut flux plus unmatched residual. -/
theorem polarized_cut_flux (hs : ∀ e : E, eps (s e) = 1) (ht : ∀ e : E, eps (t e) = -1)
    (w : V → ℂ) (q : E → ℂ) (chi : V → ℂ) :
    ∑ v : V, eps v * w v * chi v =
      (∑ e : E, q e * (chi (s e) - chi (t e))) +
        ∑ v : V, eps v * capacityResidual s t w q v * chi v := by
  have hstokes := polarized_stokes s t eps hs ht w q
  have hpair := congrArg (fun F : V → ℂ => ∑ v : V, F v * chi v) hstokes
  simp only [Pi.add_apply, polarization_apply, add_mul] at hpair
  rw [Finset.sum_add_distrib, sum_orientedBoundary_mul] at hpair
  exact hpair

omit [DecidableEq E] in
/-- **Card `(9)`.**  Under the capacity hypotheses the polarized charge is bounded by the total
unused capacity. -/
theorem abs_polarized_charge_le (hs : ∀ e : E, eps (s e) = 1) (ht : ∀ e : E, eps (t e) = -1)
    (hmod : ∀ v : V, ‖eps v‖ = 1) (w : V → ℂ) (q : E → ℂ)
    (hr : ∀ v : V, 0 ≤ (capacityResidual s t w q v).re)
    (hrre : ∀ v : V, capacityResidual s t w q v = ((capacityResidual s t w q v).re : ℂ)) :
    ‖∑ v : V, eps v * w v‖ ≤ ∑ v : V, (capacityResidual s t w q v).re := by
  rw [polarized_charge s t eps hs ht w q]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun v _ => ?_
  rw [norm_mul, hmod, one_mul]
  rw [hrre v, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr v)]
  simp

/-! ## The connected degree-zero quotient -/

/-- Augmentation. -/
def piAugmentation : (V → ℂ) →ₗ[ℂ] ℂ where
  toFun w := ∑ v : V, w v
  map_add' w u := by
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem augmentation_apply (w : V → ℂ) : piAugmentation w = ∑ v : V, w v := rfl

/-- The edge relation of the multigraph. -/
def edgeRel (u v : V) : Prop := ∃ e : E, (s e = u ∧ t e = v) ∨ (s e = v ∧ t e = u)

omit [Fintype V] in
/-- The oriented boundary of a single edge is the difference of its endpoint indicators. -/
theorem orientedBoundary_single (e : E) (v : V) :
    orientedBoundary s t (Pi.single e (1 : ℂ)) v =
      (if s e = v then 1 else 0) - (if t e = v then 1 else 0) := by
  rw [orientedBoundary_apply, Finset.sum_eq_single e]
  · rw [Pi.single_eq_same, one_mul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro hne
    exact absurd (Finset.mem_univ e) hne

omit [Fintype V] in
/-- Vertex indicator differences along edges are boundaries. -/
theorem indicator_sub_mem_range_of_edgeRel {u v : V} (h : edgeRel s t u v) :
    (fun x : V => (if u = x then (1 : ℂ) else 0) - (if v = x then 1 else 0)) ∈
      LinearMap.range (orientedBoundary s t) := by
  obtain ⟨e, he | he⟩ := h
  · refine ⟨Pi.single e 1, ?_⟩
    funext x
    rw [orientedBoundary_single, he.1, he.2]
  · refine ⟨-(Pi.single e 1), ?_⟩
    funext x
    rw [map_neg, Pi.neg_apply, orientedBoundary_single, he.1, he.2]
    ring

omit [Fintype V] in
/-- Vertex indicator differences along paths are boundaries. -/
theorem indicator_sub_mem_range_of_reachable {u v : V}
    (h : Relation.ReflTransGen (edgeRel s t) u v) :
    (fun x : V => (if u = x then (1 : ℂ) else 0) - (if v = x then 1 else 0)) ∈
      LinearMap.range (orientedBoundary s t) := by
  induction h with
  | refl =>
    have hzero : (fun x : V => (if u = x then (1 : ℂ) else 0) - (if u = x then 1 else 0)) = 0 := by
      funext x
      simp
    rw [hzero]
    exact Submodule.zero_mem _
  | @tail b c _ hbc ih =>
    have hstep := indicator_sub_mem_range_of_edgeRel s t hbc
    have hsum := Submodule.add_mem _ ih hstep
    have heq : (fun x : V => (if u = x then (1 : ℂ) else 0) - (if b = x then 1 else 0)) +
        (fun x : V => (if b = x then (1 : ℂ) else 0) - (if c = x then 1 else 0)) =
        (fun x : V => (if u = x then (1 : ℂ) else 0) - (if c = x then 1 else 0)) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rwa [heq] at hsum

/-- **Card `(8)`.**  On a connected multigraph the degree-zero boundaries are exactly the
piAugmentation kernel, so the degree-zero quotient is one dimensional. -/
theorem range_orientedBoundary_eq_ker_augmentation [Nonempty V]
    (hconn : ∀ u v : V, Relation.ReflTransGen (edgeRel s t) u v) :
    LinearMap.range (orientedBoundary s t) = LinearMap.ker (piAugmentation (V := V)) := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    rw [LinearMap.mem_ker, augmentation_apply]
    exact sum_orientedBoundary s t q
  · intro w hw
    have hsum : ∑ v : V, w v = 0 := hw
    obtain ⟨v0⟩ := ‹Nonempty V›
    have hdecomp : w = ∑ u : V, w u •
        (fun x : V => (if u = x then (1 : ℂ) else 0) - (if v0 = x then 1 else 0)) := by
      funext x
      rw [Finset.sum_apply]
      have hstep : ∀ u : V, (w u • (fun x : V => (if u = x then (1 : ℂ) else 0) -
          (if v0 = x then 1 else 0))) x
          = (if u = x then w u else 0) - w u * (if v0 = x then 1 else 0) := by
        intro u
        rw [Pi.smul_apply, smul_eq_mul, mul_sub]
        by_cases h : u = x <;> simp [h]
      rw [Finset.sum_congr rfl (fun u _ => hstep u), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ x w, if_pos (Finset.mem_univ _), ← Finset.sum_mul, hsum,
        zero_mul, sub_zero]
    rw [hdecomp]
    refine Submodule.sum_mem _ fun u _ => ?_
    exact Submodule.smul_mem _ _ (indicator_sub_mem_range_of_reachable s t (hconn u v0))

end Incidence


/-! ## The finite Abel decomposition on the ordered-prime path -/

section AbelPath

/-- **Card `(10)`.**  Prefix sums of the edge weights. -/
def prefixSum (tt : ℕ → ℂ) (m : ℕ) : ℂ := ∑ k ∈ Finset.range m, tt k

theorem sum_indicator_range (M n : ℕ) (f : ℕ → ℂ) :
    ∑ e ∈ Finset.range M, f e * (if e = n then (1 : ℂ) else 0) = if n < M then f n else 0 := by
  have hterm : ∀ e ∈ Finset.range M, f e * (if e = n then (1 : ℂ) else 0)
      = if e = n then f e else 0 := by
    intro e _
    by_cases h : e = n <;> simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range M) n f]
  simp only [Finset.mem_range]

theorem sum_indicator_shift (M n : ℕ) (f : ℕ → ℂ) :
    ∑ e ∈ Finset.range M, f e * (if e + 1 = n then (1 : ℂ) else 0)
      = if 0 < n ∧ n ≤ M then f (n - 1) else 0 := by
  cases n with
  | zero =>
    have hterm : ∀ e ∈ Finset.range M, f e * (if e + 1 = 0 then (1 : ℂ) else 0) = 0 := by
      intro e _
      simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, if_neg (by simp)]
  | succ k =>
    have hterm : ∀ e ∈ Finset.range M, f e * (if e + 1 = k + 1 then (1 : ℂ) else 0)
        = if e = k then f e else 0 := by
      intro e _
      by_cases h : e = k <;> simp [h]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range M) k f]
    simp only [Finset.mem_range]
    by_cases h : k < M
    · rw [if_pos h, if_pos ⟨Nat.succ_pos k, h⟩]
      simp
    · rw [if_neg h, if_neg]
      rintro ⟨-, h2⟩
      exact h (by omega)

theorem prefixSum_succ_sub (tt : ℕ → ℂ) (m : ℕ) :
    prefixSum tt (m + 1) - prefixSum tt m = tt m := by
  rw [prefixSum, prefixSum, Finset.sum_range_succ]
  ring

/-- **Theorem C, card `(12)` boxed.**  The exact finite Abel boundary decomposition of the
mass-shift chain on the ordered path. -/
theorem abel_boundary_decomposition (tt : ℕ → ℂ) (M n : ℕ) (hn : n ≤ M) :
    tt n =
      (∑ e ∈ Finset.range M, prefixSum tt (e + 1) *
        ((if e = n then (1 : ℂ) else 0) - (if e + 1 = n then 1 else 0)))
      + (if n = M then prefixSum tt (M + 1) else 0) := by
  have hsplit : ∀ e ∈ Finset.range M, prefixSum tt (e + 1) *
      ((if e = n then (1 : ℂ) else 0) - (if e + 1 = n then 1 else 0))
      = prefixSum tt (e + 1) * (if e = n then (1 : ℂ) else 0) -
        prefixSum tt (e + 1) * (if e + 1 = n then (1 : ℂ) else 0) := fun e _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
    sum_indicator_range M n (fun e => prefixSum tt (e + 1)),
    sum_indicator_shift M n (fun e => prefixSum tt (e + 1))]
  rcases lt_or_eq_of_le hn with hlt | heq
  · rw [if_pos hlt, if_neg (by omega : ¬ n = M)]
    cases n with
    | zero =>
      rw [if_neg (by simp)]
      have h0 := prefixSum_succ_sub tt 0
      simp only [prefixSum, Finset.range_zero, Finset.sum_empty] at h0 ⊢
      linear_combination -h0
    | succ k =>
      rw [if_pos ⟨Nat.succ_pos k, by omega⟩]
      simp only [Nat.add_sub_cancel]
      linear_combination -prefixSum_succ_sub tt (k + 1)
  · subst heq
    rw [if_neg (lt_irrefl _), if_pos rfl]
    cases n with
    | zero =>
      rw [if_neg (by simp)]
      have h0 := prefixSum_succ_sub tt 0
      simp only [prefixSum, Finset.range_zero, Finset.sum_empty] at h0 ⊢
      linear_combination -h0
    | succ k =>
      rw [if_pos ⟨Nat.succ_pos k, le_refl _⟩]
      simp only [Nat.add_sub_cancel]
      linear_combination -prefixSum_succ_sub tt (k + 1)

/-- **Theorem C, card `(13)` boxed.**  The finite Abel summation identity. -/
theorem abel_pairing (tt F : ℕ → ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), tt n * F n =
      prefixSum tt (M + 1) * F M +
        ∑ n ∈ Finset.range M, prefixSum tt (n + 1) * (F n - F (n + 1)) := by
  induction M with
  | zero => simp [prefixSum]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_range_succ (f := fun n => prefixSum tt (n + 1) * (F n - F (n + 1)))]
    have h1 : prefixSum tt (m + 1 + 1) = prefixSum tt (m + 1) + tt (m + 1) := by
      rw [prefixSum, prefixSum, Finset.sum_range_succ]
    rw [h1]
    ring

end AbelPath

/-! ## Capacity-phase separation -/

section CapacityPhase

open Filter Topology

/-- Real prefix sums of the local capacities. -/
def realPrefix (tcap : ℕ → ℝ) (m : ℕ) : ℝ := ∑ k ∈ Finset.range m, tcap k

theorem capacity_le_realPrefix {tcap : ℕ → ℝ} (hpos : ∀ n, 0 < tcap n) (m : ℕ) :
    tcap 0 ≤ realPrefix tcap (m + 1) := by
  refine Finset.single_le_sum (f := tcap) (fun i _ => (hpos i).le) ?_
  simp

theorem inv_capacity_tendsto_atTop {tcap : ℕ → ℝ} (hpos : ∀ n, 0 < tcap n)
    (hzero : Tendsto tcap atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (tcap (n + 1))⁻¹) atTop atTop := by
  have hshift : Tendsto (fun n : ℕ => tcap (n + 1)) atTop (𝓝 0) :=
    hzero.comp (tendsto_add_atTop_nat 1)
  have hwithin : Tendsto (fun n : ℕ => tcap (n + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hshift
      (Filter.Eventually.of_forall fun n => hpos (n + 1))
  exact hwithin.inv_tendsto_nhdsGT_zero

/-- **Theorem D, card `(16)` boxed.**  The Abel prefix primitive is unbounded relative to the
local edge capacity. -/
theorem tendsto_prefix_div_capacity_atTop {tcap : ℕ → ℝ} (hpos : ∀ n, 0 < tcap n)
    (hzero : Tendsto tcap atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => realPrefix tcap (n + 1) / tcap (n + 1)) atTop atTop := by
  refine tendsto_atTop_mono (f := fun n : ℕ => tcap 0 * (tcap (n + 1))⁻¹) (fun n => ?_) ?_
  · rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (capacity_le_realPrefix hpos n)
      (inv_nonneg.mpr (hpos (n + 1)).le)
  · exact (inv_capacity_tendsto_atTop hpos hzero).const_mul_atTop (hpos 0)

/-- **Theorem D, card `(17)` boxed.**  The log-gap work of the Abel prefix primitive diverges. -/
theorem tendsto_logGapWork_atTop {tcap : ℕ → ℝ} (hpos : ∀ n, 0 < tcap n)
    {lam : ℕ → ℝ} (hmono : Monotone lam) (hlam : Tendsto lam atTop atTop) :
    Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range N, realPrefix tcap (n + 1) * (lam (n + 1) - lam n)) atTop atTop := by
  have hlower : ∀ N : ℕ, tcap 0 * (lam N - lam 0) ≤
      ∑ n ∈ Finset.range N, realPrefix tcap (n + 1) * (lam (n + 1) - lam n) := by
    intro N
    have htel : tcap 0 * (lam N - lam 0)
        = ∑ n ∈ Finset.range N, tcap 0 * (lam (n + 1) - lam n) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]
    rw [htel]
    refine Finset.sum_le_sum fun n _ => ?_
    refine mul_le_mul_of_nonneg_right (capacity_le_realPrefix hpos n) ?_
    exact sub_nonneg.mpr (hmono (Nat.le_succ n))
  refine tendsto_atTop_mono hlower ?_
  have hshift : Tendsto (fun N : ℕ => lam N - lam 0) atTop atTop := by
    have hadd := Filter.tendsto_atTop_add_const_right atTop (-lam 0) hlam
    exact hadd.congr fun N => by ring
  exact hshift.const_mul_atTop (hpos 0)

/-- **Theorem D, card `(17a)` boxed.**  The Abel prefix primitive lies in no fixed local-capacity
ball. -/
theorem not_bounded_local_capacity {tcap : ℕ → ℝ} (hpos : ∀ n, 0 < tcap n)
    (hzero : Tendsto tcap atTop (𝓝 0)) :
    ¬ ∃ M : ℝ, ∀ n : ℕ, realPrefix tcap (n + 1) ≤ M * tcap (n + 1) := by
  rintro ⟨M, hM⟩
  have hdiv := tendsto_prefix_div_capacity_atTop hpos hzero
  obtain ⟨n, hn⟩ := (hdiv.eventually_gt_atTop M).exists
  have hle : realPrefix tcap (n + 1) / tcap (n + 1) ≤ M := by
    rw [div_le_iff₀ (hpos (n + 1))]
    exact hM n
  linarith

/-! ### The ordered-prime instantiation -/

/-- The `n`-th prime. -/
def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem primeAt_prime (n : ℕ) : (primeAt n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

theorem primeAt_strictMono : StrictMono primeAt :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

theorem one_lt_primeAt (n : ℕ) : (1 : ℝ) < (primeAt n : ℝ) := by
  exact_mod_cast (primeAt_prime n).one_lt

/-- **Card `(10)`.**  The log of the `n`-th prime. -/
def primeLog (n : ℕ) : ℝ := Real.log (primeAt n)

/-- **Card `(10)`.**  The local mass capacity `log p / √p`. -/
def primeMassCapacity (n : ℕ) : ℝ := Real.log (primeAt n) / Real.sqrt (primeAt n)

theorem primeMassCapacity_pos (n : ℕ) : 0 < primeMassCapacity n := by
  refine div_pos (Real.log_pos (one_lt_primeAt n)) (Real.sqrt_pos.mpr ?_)
  linarith [one_lt_primeAt n]

theorem primeLog_monotone : Monotone primeLog := by
  intro a b hab
  refine Real.log_le_log (by linarith [one_lt_primeAt a]) ?_
  exact_mod_cast primeAt_strictMono.monotone hab

theorem tendsto_primeAt_atTop : Tendsto (fun n : ℕ => (primeAt n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp primeAt_strictMono.tendsto_atTop

theorem tendsto_primeLog_atTop : Tendsto primeLog atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_primeAt_atTop

theorem tendsto_primeMassCapacity_zero : Tendsto primeMassCapacity atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    have h := RHTower.ForbiddenSupport.tendsto_logRpow_div_sqrt 1
    refine h.congr fun x => ?_
    rw [Real.rpow_one]
  exact hreal.comp tendsto_primeAt_atTop

/-- **Theorem D, card `(16)` boxed, at the primes.** -/
theorem tendsto_primePrefix_div_capacity_atTop :
    Tendsto (fun n : ℕ => realPrefix primeMassCapacity (n + 1) / primeMassCapacity (n + 1))
      atTop atTop :=
  tendsto_prefix_div_capacity_atTop primeMassCapacity_pos tendsto_primeMassCapacity_zero

/-- **Theorem D, card `(17)` boxed, at the primes.** -/
theorem tendsto_primeLogGapWork_atTop :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      realPrefix primeMassCapacity (n + 1) * (primeLog (n + 1) - primeLog n)) atTop atTop :=
  tendsto_logGapWork_atTop primeMassCapacity_pos primeLog_monotone tendsto_primeLog_atTop

/-- **Theorem D, card `(17a)` boxed, at the primes.** -/
theorem not_bounded_prime_local_capacity :
    ¬ ∃ M : ℝ, ∀ n : ℕ,
      realPrefix primeMassCapacity (n + 1) ≤ M * primeMassCapacity (n + 1) :=
  not_bounded_local_capacity primeMassCapacity_pos tendsto_primeMassCapacity_zero

end CapacityPhase

end HTGeometry.ConstraintRelativity

end
