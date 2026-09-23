/-
# Böttcher tower — basin connectedness, reduced to the Riemann–Hurwitz step

`harmonic_exterior_unique` (hence the E1/E-rigidity chain `c_eq_of_filledJulia_eq`) carries the
hypothesis `IsPreconnected (filledJulia c)ᶜ` — the basin of `∞` is connected. This file reduces that
to a single per-step input.

`basin = ⋃ₙ escapeLevel c n`, an **increasing** union of the open sets `escapeLevel c n =
{z : f_c^[n] z ∈ escapeOpen}`, all containing a common deep point near `∞`; so the union is
preconnected as soon as each level is (`isPreconnected_iUnion`). The levels are recursive —
`escapeLevel c 0 = escapeOpen` (connected) and `escapeLevel c (n+1) = f_c⁻¹(escapeLevel c n)` — so the
whole thing reduces to the **Riemann–Hurwitz step**: the `f_c`-preimage of a connected level is
connected. That step (the branched-cover / critical-value structure of `z²+c`) is the lone remaining
input, isolated here as `hstep`.

New file (hRigid connected lane); consumes `BottcherBasin`, `SquareFree`.
-/
import GaloisForLFunctions.Bottcher.BottcherBasin
import GaloisForLFunctions.Bottcher.SquareFree

open Set Metric

namespace Bottcher

/-- The `n`-th escape level `{z : f_c^[n] z ∈ escapeOpen}` (the points escaping within `n` steps). -/
def escapeLevel (c : ℂ) (n : ℕ) : Set ℂ := {z | (quadratic c)^[n] z ∈ escapeOpen c}

/-- The basin `ℂ ∖ K_c` is the union of the escape levels. -/
theorem compl_filledJulia_eq_iUnion_level (c : ℂ) :
    (filledJulia c)ᶜ = ⋃ n, escapeLevel c n := by
  rw [← basin_eq_compl_filledJulia]
  ext z
  simp only [basin, escapeLevel, Set.mem_setOf_eq, Set.mem_iUnion]

/-- `escapeLevel c 0 = escapeOpen c`. -/
theorem escapeLevel_zero (c : ℂ) : escapeLevel c 0 = escapeOpen c := by
  ext z; simp only [escapeLevel, Function.iterate_zero, id_eq, Set.mem_setOf_eq]

/-- **Mandelbrot parameters keep the critical value out of every escape level.** In this project's
normalization `c ∈ mandelbrot` means the critical point `0` has bounded orbit. Hence the critical
value `c = f_c(0)` and all of its forward iterates lie in `filledJulia c`, so none can lie in the far
escape set used to define `escapeLevel c n`. -/
theorem criticalValue_not_mem_escapeLevel_of_mem_mandelbrot {c : ℂ} (hc : c ∈ mandelbrot) (n : ℕ) :
    c ∉ escapeLevel c n := by
  intro hesc
  have hcK : c ∈ filledJulia c := by
    have h1 : (quadratic c)^[1] (0 : ℂ) ∈ filledJulia c := filledJulia_forward hc 1
    simpa [Function.iterate_one, quadratic_apply] using h1
  have hiterK : (quadratic c)^[n] c ∈ filledJulia c := filledJulia_forward hcK n
  obtain ⟨hcn, h2n⟩ := mem_escapeOpen_regime hesc
  exact not_mem_filledJulia hcn h2n hiterK

/-- The bundled connected-lane hypothesis consumed by the `ρ` tower, from `c ∈ mandelbrot`. -/
theorem criticalValue_not_mem_escapeLevels_of_mem_mandelbrot {c : ℂ} (hc : c ∈ mandelbrot) :
    ∀ n, c ∉ escapeLevel c n :=
  fun n => criticalValue_not_mem_escapeLevel_of_mem_mandelbrot hc n

/-- **Recursive structure**: `escapeLevel c (n+1) = f_c⁻¹(escapeLevel c n)`. -/
theorem escapeLevel_succ (c : ℂ) (n : ℕ) :
    escapeLevel c (n + 1) = (quadratic c) ⁻¹' escapeLevel c n := by
  ext z
  simp only [escapeLevel, Set.mem_preimage, Set.mem_setOf_eq, Function.iterate_succ,
    Function.comp_apply]

/-- A fixed deep point lies in every escape level (its orbit only grows). -/
theorem deep_mem_escapeLevel (c : ℂ) (n : ℕ) :
    ((max 2 ‖c‖ + 1 : ℝ) : ℂ) ∈ escapeLevel c n := by
  have hnn : (0 : ℝ) ≤ max 2 ‖c‖ := le_trans (by norm_num) (le_max_left _ _)
  have hz0 : ‖((max 2 ‖c‖ + 1 : ℝ) : ℂ)‖ = max 2 ‖c‖ + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hlt : max 2 ‖c‖ < ‖((max 2 ‖c‖ + 1 : ℝ) : ℂ)‖ := by rw [hz0]; linarith
  have hc : ‖c‖ ≤ ‖((max 2 ‖c‖ + 1 : ℝ) : ℂ)‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hlt)
  have h2 : (2 : ℝ) < ‖((max 2 ‖c‖ + 1 : ℝ) : ℂ)‖ := lt_of_le_of_lt (le_max_left _ _) hlt
  show (quadratic c)^[n] _ ∈ escapeOpen c
  rw [escapeOpen, Set.mem_setOf_eq]
  exact lt_of_lt_of_le hlt (norm_le_orbit hc h2 n)

/-- **Basin-connectedness reduced to per-level connectedness.** If every escape level is preconnected,
the basin `ℂ ∖ K_c` is preconnected (increasing union with a common deep point). -/
theorem isPreconnected_compl_filledJulia_of_levels (c : ℂ)
    (hlev : ∀ n, IsPreconnected (escapeLevel c n)) :
    IsPreconnected (filledJulia c)ᶜ := by
  rw [compl_filledJulia_eq_iUnion_level]
  exact isPreconnected_iUnion ⟨((max 2 ‖c‖ + 1 : ℝ) : ℂ),
    Set.mem_iInter.mpr (fun n => deep_mem_escapeLevel c n)⟩ hlev

/-- **All escape levels are preconnected — reduced to the Riemann–Hurwitz step `hstep`.** The base
case is `escapeLevel c 0 = escapeOpen c` (connected); the inductive step `escapeLevel c (n+1) =
f_c⁻¹(escapeLevel c n)` is the genuine branched-cover connectedness `hstep` (the `f_c`-preimage of an
escape level — an exterior whose complement carries the critical value — is connected). -/
theorem isPreconnected_escapeLevel_of_step (c : ℂ)
    (hstep : ∀ n, IsPreconnected (escapeLevel c n) → IsPreconnected (escapeLevel c (n + 1))) :
    ∀ n, IsPreconnected (escapeLevel c n) := by
  intro n
  induction n with
  | zero => rw [escapeLevel_zero]; exact (isConnected_escapeOpen c).isPreconnected
  | succ k ih => exact hstep k ih

/-- **Basin-connectedness from the Riemann–Hurwitz step.** The full reduction: the single remaining
input for `IsPreconnected (filledJulia c)ᶜ` is that `f_c⁻¹` carries each escape level (an exterior
with the critical value in its complement) to a connected set — the branched-cover / critical-value
structure of `z²+c`. -/
theorem isPreconnected_compl_filledJulia_of_step (c : ℂ)
    (hstep : ∀ n, IsPreconnected (escapeLevel c n) → IsPreconnected (escapeLevel c (n + 1))) :
    IsPreconnected (filledJulia c)ᶜ :=
  isPreconnected_compl_filledJulia_of_levels c (isPreconnected_escapeLevel_of_step c hstep)

/-- **The Riemann–Hurwitz step.** The `f_c`-preimage of a (connected) escape level is connected. The
connectedness comes from the exterior topology (the `z²` monodromy around `∞`), not from the critical
value: writing `P = f_c⁻¹(V)`, the component `U` of a deep point satisfies `f_c(U)=V` (open + proper-
closed ⟹ clopen ⟹ all of the connected `V`), and every `w∈P` has `f_c(w)=f_c(u)` for some `u∈U`, so
`w=±u`; since `U` is symmetric (`±z_d` lie in the connected `escapeOpen ⊆ U`), `w∈U`. Hence `P=U`. -/
theorem isPreconnected_preimage_escapeLevel (c : ℂ) (n : ℕ)
    (hVconn : IsConnected (escapeLevel c n)) :
    IsPreconnected (escapeLevel c (n + 1)) := by
  rw [escapeLevel_succ]
  have hcont : Continuous (quadratic c) := by unfold quadratic; fun_prop
  have hcontIt : Continuous (quadratic c)^[n] := hcont.iterate n
  set V : Set ℂ := escapeLevel c n with hVdef
  have hVopen : IsOpen V := by
    rw [hVdef, escapeLevel]; exact (isOpen_escapeOpen c).preimage hcontIt
  set P : Set ℂ := (quadratic c) ⁻¹' V with hPdef
  have hPopen : IsOpen P := hVopen.preimage hcont
  -- open map + proper map for quadratic
  have hfopen : IsOpenMap (quadratic c) := by
    have han : AnalyticOnNhd ℂ (quadratic c) Set.univ := fun z _ => analyticAt_quadratic c z
    refine (han.is_constant_or_isOpenMap).resolve_left ?_
    rintro ⟨x, hx⟩
    have h0 := hx 0; have h1 := hx 1
    simp only [quadratic_apply] at h0 h1
    apply (by norm_num : (1:ℂ) ≠ 0); linear_combination h1 - h0
  have hfproper : IsProperMap (quadratic c) := by
    have := quadratic_iterate_isProperMap c 1; simpa using this
  -- P is symmetric under z ↦ -z
  have hPsymm : ∀ w, w ∈ P → -w ∈ P := by
    intro w hw
    rw [hPdef, Set.mem_preimage, quadratic_apply] at hw ⊢
    rwa [even_two.neg_pow]
  -- deep point and its component
  set z_d : ℂ := ((max 2 ‖c‖ + 1 : ℝ) : ℂ) with hzd
  have hz_dP : z_d ∈ P := by
    have := deep_mem_escapeLevel c (n + 1); rwa [escapeLevel_succ] at this
  set U : Set ℂ := connectedComponentIn P z_d with hUdef
  have hUopen : IsOpen U := hPopen.connectedComponentIn
  have hUsub : U ⊆ P := connectedComponentIn_subset P z_d
  have hz_dU : z_d ∈ U := mem_connectedComponentIn hz_dP
  have hUconn : IsPreconnected U := isPreconnected_connectedComponentIn
  -- escapeOpen ⊆ U  (so ±z_d ∈ U)
  have hescP : escapeOpen c ⊆ P := by
    intro w hw
    obtain ⟨hcw, hzw⟩ := mem_escapeOpen_regime hw
    rw [hPdef, Set.mem_preimage, hVdef, escapeLevel, Set.mem_setOf_eq,
      ← Function.iterate_succ_apply, escapeOpen, Set.mem_setOf_eq]
    exact lt_of_lt_of_le hw (norm_le_orbit hcw hzw (n + 1))
  have hz_desc : z_d ∈ escapeOpen c := by
    rw [escapeOpen, Set.mem_setOf_eq, hzd, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by have : (0:ℝ) ≤ max 2 ‖c‖ := le_trans (by norm_num) (le_max_left _ _); linarith)]
    linarith
  have hescU : escapeOpen c ⊆ U :=
    (isConnected_escapeOpen c).isPreconnected.subset_connectedComponentIn hz_desc hescP
  -- closure-membership helper: closure U ∩ P ⊆ U
  have hcl : ∀ u, u ∈ closure U → u ∈ P → u ∈ U := by
    intro u hucl huP
    have hov : (connectedComponentIn P u ∩ U).Nonempty :=
      mem_closure_iff_nhds.mp hucl _ (hPopen.connectedComponentIn.mem_nhds (mem_connectedComponentIn huP))
    obtain ⟨y, hy1, hy2⟩ := hov
    have e1 : connectedComponentIn P u = connectedComponentIn P y := connectedComponentIn_eq hy1
    have e2 : connectedComponentIn P z_d = connectedComponentIn P y :=
      connectedComponentIn_eq (hUdef ▸ hy2 : y ∈ connectedComponentIn P z_d)
    have heq : connectedComponentIn P u = U := by rw [e1, ← e2, ← hUdef]
    rw [← heq]; exact mem_connectedComponentIn huP
  -- f(U) closed in V
  have hSsubV : (quadratic c) '' U ⊆ V := by rintro _ ⟨u, hu, rfl⟩; exact hUsub hu
  have hSclosedV : V ∩ closure ((quadratic c) '' U) ⊆ (quadratic c) '' U := by
    intro v hv
    have hcl1 : closure ((quadratic c) '' U) ⊆ (quadratic c) '' closure U :=
      closure_minimal (Set.image_mono subset_closure) (hfproper.isClosedMap _ isClosed_closure)
    obtain ⟨u, hucl, hfu⟩ := hcl1 hv.2
    have huP : u ∈ P := by rw [hPdef, Set.mem_preimage, hfu]; exact hv.1
    exact ⟨u, hcl u hucl huP, hfu⟩
  -- f(U) = V (clopen on the connected V)
  have hfUV : (quadratic c) '' U = V := by
    set S : Set ℂ := (quadratic c) '' U with hSdef
    refine Set.Subset.antisymm hSsubV ?_
    refine hVconn.isPreconnected.subset_left_of_subset_union (u := S) (v := (closure S)ᶜ)
      (hfopen U hUopen) (isOpen_compl_iff.mpr (isClosed_closure (s := S))) ?_ ?_ ?_
    · rw [Set.disjoint_left]; intro x hx hx'; exact hx' (subset_closure hx)
    · intro v hv
      by_cases hvS : v ∈ S
      · exact Or.inl hvS
      · exact Or.inr (fun hcc => hvS (hSclosedV ⟨hv, hcc⟩))
    · refine ⟨quadratic c z_d, ?_, ⟨z_d, hz_dU, rfl⟩⟩
      have hh := hz_dP; rw [hPdef, Set.mem_preimage] at hh; exact hh
  -- P = U
  have hPU : P = U := by
    refine Set.Subset.antisymm (fun w hwP => ?_) hUsub
    have hfwV : quadratic c w ∈ V := hwP
    rw [← hfUV] at hfwV
    obtain ⟨u, huU, hfuw⟩ := hfwV
    have hsq : u ^ (2 : ℕ) = w ^ (2 : ℕ) := by
      have : quadratic c u = quadratic c w := hfuw
      rw [quadratic_apply, quadratic_apply] at this; linear_combination this
    have : u = w ∨ u = -w := by
      rcases mul_eq_zero.mp (by linear_combination hsq : (u - w) * (u + w) = 0) with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    rcases this with h | h
    · rwa [← h]
    · -- w = -u, and -U ⊆ U
      have hnegU : (fun x => -x) '' U ⊆ U := by
        have hpre : IsPreconnected ((fun x => -x) '' U) :=
          hUconn.image _ (continuous_neg.continuousOn)
        have hsubP : (fun x => -x) '' U ⊆ P := by
          rintro _ ⟨x, hx, rfl⟩; exact hPsymm x (hUsub hx)
        have hnzd : -z_d ∈ (fun x => -x) '' U := ⟨z_d, hz_dU, rfl⟩
        have hnzdU : -z_d ∈ U := hescU (by
          rw [escapeOpen, Set.mem_setOf_eq, norm_neg]; exact hz_desc)
        have hun : IsPreconnected ((fun x => -x) '' U ∪ U) :=
          hpre.union (-z_d) hnzd hnzdU hUconn
        have : ((fun x => -x) '' U ∪ U) ⊆ U :=
          hun.subset_connectedComponentIn (Or.inr hz_dU) (Set.union_subset hsubP hUsub)
        exact (Set.subset_union_left).trans this
      have : w = -u := by rw [h]; ring
      rw [this]; exact hnegU ⟨u, huU, rfl⟩
  rw [hPU]; exact hUconn

/-- **Basin-connectedness, UNCONDITIONAL.** `ℂ ∖ K_c` is preconnected (the basin of `∞` is connected),
discharging the hypothesis of the E1/E-rigidity chain. -/
theorem isPreconnected_compl_filledJulia (c : ℂ) : IsPreconnected (filledJulia c)ᶜ :=
  isPreconnected_compl_filledJulia_of_step c
    (fun n hn => isPreconnected_preimage_escapeLevel c n ⟨⟨_, deep_mem_escapeLevel c n⟩, hn⟩)


end Bottcher
