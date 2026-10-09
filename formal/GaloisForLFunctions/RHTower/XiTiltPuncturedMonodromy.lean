import GaloisForLFunctions.RHTower.XiMarkedConjugatePackets
import GaloisForLFunctions.RHTower.XiMarkedMeridian
import GaloisForLFunctions.RHTower.XiFiniteCoverMonodromy

/-!
# Finite monodromy of a tilted Xi source over an arbitrary finitely punctured plane

Let `d_a(s) = ξ(s) e^{-as}`, let `F ⊂ ℂ` be finite, `V_F = ℂ ∖ ({0} ∪ F)` and
`U_F = d_a⁻¹(V_F)`.  For every homomorphism `f` from `π₁(V_F)` to a finite group, the monodromy
image of `π₁(U_F)` has the same image as `π₁(V_F)`.

Proof.  Every loop of zero winding about `0` has a closed logarithmic lift; a logarithmic inverse
island `d_a ∘ h = exp` on a disk containing it carries it to a source loop, so after one common
conjugation every finite packet of the zero-winding kernel lies in the image.  A small circle at a
simple Xi zero has winding one, so the image also exhausts the winding quotient.
-/

open Set Filter Topology Metric Complex unitInterval
open GaloisForLFunctions.HTGeometry Pi1CMinusZero RHTower.XiMarkedMonodromy

namespace RHTower.XiTiltMonodromy

noncomputable section

variable (a : ℝ) (F : Finset ℂ)

/-- `V_F = ℂ ∖ ({0} ∪ F)`. -/
abbrev PTarget (F : Finset ℂ) := {z : ℂ // z ≠ 0 ∧ z ∉ F}

/-- `U_F = d_a⁻¹(V_F)`. -/
def psourceSet : Set ℂ := {s | xi s ≠ 0 ∧ ∀ c ∈ F, c ≠ 0 → value a s ≠ c}

abbrev PSource := psourceSet a F

theorem value_ne_zero_of_mem {s : ℂ} (hs : s ∈ psourceSet a F) : value a s ≠ 0 :=
  mul_ne_zero hs.1 (Complex.exp_ne_zero _)

/-- `d_a : U_F → V_F`. -/
def ptilt : C(PSource a F, PTarget F) :=
  ⟨fun s => ⟨value a s, value_ne_zero_of_mem a F s.2, fun h =>
      s.2.2 _ h (value_ne_zero_of_mem a F s.2) rfl⟩,
    ((value_differentiable a).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem ptilt_apply (s : PSource a F) : (ptilt a F s : ℂ) = value a s := rfl

/-- The inclusion `V_F → ℂ^*`. -/
def ptargetToPunctured : C(PTarget F, Cs) :=
  ⟨fun z => ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩

private theorem exists_xi_zero : ∃ ρ : ℂ, xi ρ = 0 := by
  obtain ⟨t, -, -, hz, -⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi 0
  exact ⟨_, hz⟩

theorem psourceSet_pathConnected : IsPathConnected (psourceSet a F) := by
  obtain ⟨ρ, hρ⟩ := exists_xi_zero
  have hxi : {s : ℂ | xi s = 0}.Countable :=
    countable_setOf_eq_zero_of_differentiable xi_differentiable
      (x := 0) (by rw [xi_zero]; norm_num)
  have hv (c : ℂ) (hc : c ≠ 0) : {s : ℂ | value a s = c}.Countable := by
    have h := countable_setOf_eq_zero_of_differentiable
      ((value_differentiable a).sub_const c) (x := ρ)
      (by simp [value, hρ, hc])
    simpa only [sub_eq_zero] using h
  have hc : ({s : ℂ | xi s = 0} ∪ ⋃ c ∈ F.filter (· ≠ 0), {s : ℂ | value a s = c}).Countable :=
    hxi.union ((F.filter (· ≠ 0)).countable_toSet.biUnion fun c hc =>
      hv c (Finset.mem_filter.mp hc).2)
  have hp := hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
  convert hp using 1
  ext s
  simp only [psourceSet, mem_setOf_eq, mem_compl_iff, mem_union, mem_iUnion,
    exists_prop, not_or, not_exists, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun c hc hv => ?_⟩
    obtain ⟨hcF, hc0⟩ := Finset.mem_filter.mp hc
    exact h2 c hcF hc0 hv
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun c hc hc0 hv => h2 c (Finset.mem_filter.mpr ⟨hc, hc0⟩) hv⟩

instance psource_pathConnectedSpace : PathConnectedSpace (PSource a F) :=
  isPathConnected_iff_pathConnectedSpace.mp (psourceSet_pathConnected a F)

theorem isOpen_psourceSet : IsOpen (psourceSet a F) := by
  have h1 : IsOpen {s : ℂ | xi s ≠ 0} := isOpen_ne_fun xi_differentiable.continuous continuous_const
  have h2 : IsOpen (⋂ c ∈ F.filter (· ≠ 0), {s : ℂ | value a s ≠ c}) :=
    isOpen_biInter_finset fun c _ =>
      isOpen_ne_fun (value_differentiable a).continuous continuous_const
  convert h1.inter h2 using 1
  ext s
  simp [psourceSet]

instance psource_locallyPathConnectedSpace : LocallyPathConnectedSpace (PSource a F) :=
  (isOpen_psourceSet a F).locallyPathConnectedSpace

theorem ptarget_isOpen : IsOpen {z : ℂ | z ≠ 0 ∧ z ∉ F} := by
  have : {z : ℂ | z ≠ 0 ∧ z ∉ F} = ({0} ∪ (F : Set ℂ))ᶜ := by ext z; simp [not_or]
  rw [this]
  exact ((Set.finite_singleton 0).union F.finite_toSet).isClosed.isOpen_compl

instance ptarget_locallyPathConnectedSpace : LocallyPathConnectedSpace (PTarget F) :=
  (ptarget_isOpen F).locallyPathConnectedSpace

instance ptarget_pathConnectedSpace : PathConnectedSpace (PTarget F) := by
  have hc : ({0} ∪ (F : Set ℂ)).Countable := (Set.countable_singleton 0).union F.countable_toSet
  have hp := hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)
  have he : ({0} ∪ (F : Set ℂ))ᶜ = {z : ℂ | z ≠ 0 ∧ z ∉ F} := by ext z; simp [not_or]
  rw [he] at hp
  exact isPathConnected_iff_pathConnectedSpace.mp hp

/-- A basepoint of `U_F`. -/
def pbase : PSource a F := ⟨_, (psourceSet_pathConnected a F).nonempty.some_mem⟩

/-- The monodromy homomorphism of `d_a : U_F → V_F`. -/
def pmap : FundamentalGroup (PSource a F) (pbase a F) →*
    FundamentalGroup (PTarget F) (ptilt a F (pbase a F)) :=
  FundamentalGroup.mapOfEq (ptilt a F) rfl

/-- Winding about `0` on `V_F`. -/
def pwind (b : PTarget F) : FundamentalGroup (PTarget F) b →* Multiplicative ℤ :=
  normalizedWindingHom (ptargetToPunctured F) b

/-- Xi on `U_F`. -/
def pxi : C(PSource a F, Cs) :=
  ⟨fun s => ⟨xi s, s.2.1⟩, (xi_differentiable.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The target winding of a source loop is its Xi winding. -/
theorem pwind_pmap (q : FundamentalGroup (PSource a F) (pbase a F)) :
    pwind F _ (pmap a F q) = normalizedWindingHom (pxi a F) (pbase a F) q := by
  change ((normalizedWindingHom (ptargetToPunctured F) _).comp
    (FundamentalGroup.mapOfEq (ptilt a F) rfl)) q = _
  rw [normalizedWindingHom_comp_mapOfEq]
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [normalizedWindingHom_mk, normalizedWindingHom_mk]
    apply congrArg Multiplicative.ofAdd
    have hxc : Continuous (fun s : PSource a F => xi (s : ℂ)) :=
      xi_differentiable.continuous.comp continuous_subtype_val
    have hxn : ∀ s : PSource a F, xi (s : ℂ) ≠ 0 := fun s => s.2.1
    have hmc : Continuous (fun s : PSource a F => -(a : ℂ) * (s : ℂ)) := by fun_prop
    have hec := Complex.continuous_exp.comp hmc
    have hen : ∀ s : PSource a F, Complex.exp (-(a : ℂ) * (s : ℂ)) ≠ 0 :=
      fun s => Complex.exp_ne_zero _
    change Bottcher.wind (fun s : PSource a F => xi (s : ℂ) *
      Complex.exp (-(a : ℂ) * (s : ℂ))) (hxc.mul hec)
        (fun s => mul_ne_zero (hxn s) (hen s)) p = Bottcher.wind _ hxc hxn p
    rw [Bottcher.wind_mul, Bottcher.wind_exp, add_zero] <;> assumption

/-- A finite zero-winding packet at any target basepoint lifts to source loops at one point. -/
theorem exists_psource_loop_packet {ι : Type*} [Finite ι] {base : PTarget F}
    (p : ι → Path base base)
    (hp : ∀ i, Bottcher.wind (fun z : PTarget F => (z : ℂ))
      continuous_subtype_val (fun z => z.2.1) (p i) = 0) :
    ∃ s : PSource a F, ∃ hs : ptilt a F s = base, ∃ l : ι → Path s s, ∀ i,
      ((l i).map (ptilt a F).continuous).cast hs.symm hs.symm = p i := by
  classical
  obtain ⟨M, hM, w0, hwM, hw0, L, hL⟩ := exists_bounded_closed_log_lift_packet_at_base
    (fun i => (p i).map (ptargetToPunctured F).continuous) hp
  obtain ⟨h, hhd, hh⟩ := exists_xi_tilt_exp_lift_ball a M 0 hM
  have h0 : w0 ∈ ball 0 M := by simpa using hwM
  have hLmem (i : ι) (t : I) : L i t ∈ ball 0 M := by
    simpa using (hL i t).1
  have hsource (w : ℂ) (hw : w ∈ ball 0 M) (he : Complex.exp w ∉ F) :
      h w ∈ psourceSet a F := by
    have hval : value a (h w) = Complex.exp w := (hh w hw).2
    refine ⟨?_, fun c hc _ hvc => he (hval ▸ hvc ▸ hc)⟩
    intro hz
    have := hval
    rw [value, hz, zero_mul] at this
    exact Complex.exp_ne_zero w this.symm
  let s : PSource a F := ⟨h w0, hsource w0 h0 (by rw [hw0]; exact base.2.2)⟩
  have hs : ptilt a F s = base := by
    apply Subtype.ext
    exact (hh w0 h0).2.trans hw0
  have hlexp (i : ι) (t : I) : Complex.exp (L i t) ∉ F := by
    rw [(hL i t).2]
    exact (p i t).2.2
  let l (i : ι) : Path s s :=
    { toFun := fun t => ⟨h (L i t), hsource (L i t) (hLmem i t) (hlexp i t)⟩
      continuous_toFun :=
        (hhd.continuousOn.comp_continuous (L i).continuous (hLmem i)).subtype_mk _
      source' := by apply Subtype.ext; change h (L i 0) = h w0; rw [(L i).source]
      target' := by apply Subtype.ext; change h (L i 1) = h w0; rw [(L i).target] }
  refine ⟨s, hs, l, fun i => ?_⟩
  apply Path.ext
  funext t
  apply Subtype.ext
  exact (hh (L i t) (hLmem i t)).2.trans (hL i t).2

/-- One common conjugator places a finite zero-winding packet into the monodromy image. -/
theorem exists_common_conjugate_ppacket {ι : Type*} [Finite ι]
    (q : ι → FundamentalGroup (PTarget F) (ptilt a F (pbase a F)))
    (hq : ∀ i, pwind F _ (q i) = 1) :
    ∃ g, ∀ i, g * q i * g⁻¹ ∈ (pmap a F).range := by
  classical
  have hrep (i : ι) : ∃ p : Path (ptilt a F (pbase a F)) (ptilt a F (pbase a F)),
      FundamentalGroup.fromPath ⟦p⟧ = q i := Quotient.exists_rep (q i)
  choose p hp using hrep
  have hw (i : ι) : Bottcher.wind (fun z : PTarget F => (z : ℂ))
      continuous_subtype_val (fun z => z.2.1) (p i) = 0 := by
    have h := normalizedWindingHom_mk (ptargetToPunctured F) (p i)
    change pwind F _ (FundamentalGroup.fromPath ⟦p i⟧) =
      Multiplicative.ofAdd (Bottcher.wind (fun z : PTarget F => (z : ℂ))
        continuous_subtype_val (fun z => z.2.1) (p i)) at h
    rw [hp i, hq i] at h
    exact congrArg Multiplicative.toAdd h.symm
  obtain ⟨s, hs, l, hl⟩ := exists_psource_loop_packet a F p hw
  let α := PathConnectedSpace.somePath (pbase a F) s
  let g : FundamentalGroup (PTarget F) (ptilt a F (pbase a F)) := .fromPath
    ⟦(α.map (ptilt a F).continuous).cast rfl hs.symm⟧
  let u (i : ι) := FundamentalGroup.fundamentalGroupMulEquivOfPath α.symm
    (FundamentalGroup.fromPath ⟦l i⟧)
  refine ⟨g⁻¹, fun i => ⟨u i, ?_⟩⟩
  have hi := fundamentalGroup_mapOfEq_transport (ptilt a F) (rfl : ptilt a F (pbase a F) = _) hs α
    (l i)
  change FundamentalGroup.mapOfEq (ptilt a F) rfl (u i) =
    g⁻¹ * FundamentalGroup.mapOfEq (ptilt a F) hs (FundamentalGroup.fromPath ⟦l i⟧) * g at hi
  rw [fundamentalGroup_mapOfEq_mk, hl i, hp i] at hi
  rw [inv_inv]
  exact hi

/-- Every finite group sees the complete zero-winding kernel. -/
theorem finite_image_contains_kernel {G : Type*} [Group G] [Finite G]
    (f : FundamentalGroup (PTarget F) (ptilt a F (pbase a F)) →* G)
    (q : FundamentalGroup (PTarget F) (ptilt a F (pbase a F))) (hq : pwind F _ q = 1) :
    f q ∈ (pmap a F).range.map f := by
  classical
  have hpacket (T : Finset (FundamentalGroup (PTarget F) (ptilt a F (pbase a F))))
      (hT : ∀ x ∈ T, x ∈ (pwind F _).ker) :
      ∃ g, ∀ x ∈ T, g * x * g⁻¹ ∈ (pmap a F).range := by
    obtain ⟨g, hg⟩ := exists_common_conjugate_ppacket a F (fun x : T => x.val)
      (fun x => hT x x.2)
    exact ⟨g, fun x hx => hg ⟨x, hx⟩⟩
  have hh := map_le_of_finite_normal_packets (pwind F _).ker (pmap a F).range hpacket f
  exact hh ⟨q, hq, rfl⟩

/-- A small circle at an actual simple Xi zero is a source meridian of Xi winding one. -/
theorem exists_plocal_winding_one :
    ∃ s : PSource a F, ∃ p : Path s s,
      normalizedWindingHom (pxi a F) s (FundamentalGroup.fromPath ⟦p⟧) =
        Multiplicative.ofAdd 1 := by
  classical
  obtain ⟨t, _, _, hz, ho⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi 0
  let ρ := DeletionMixedRefinement.criticalResponsePoint t
  have hzero : xi ρ = 0 := hz
  obtain ⟨R, hR, u, _, hu, hfac⟩ := xi_peel_ball ρ
  obtain ⟨W, hW, hw⟩ := windingNumber_xi_zero ρ
  have hev : ∀ᶠ z in 𝓝 ρ, ∀ c ∈ F.filter (· ≠ 0), value a z ≠ c := by
    apply (Filter.eventually_all_finset _).mpr
    intro c hc
    apply (value_differentiable a).continuous.continuousAt.eventually_ne
    simpa [value, hzero, eq_comm] using (Finset.mem_filter.mp hc).2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨r, hr, hrb⟩ := exists_between (lt_min hε (lt_min hR hW))
  have hrε := (lt_min_iff.mp hrb).1
  have hrR := (lt_min_iff.mp (lt_min_iff.mp hrb).2).1
  have hrW := (lt_min_iff.mp (lt_min_iff.mp hrb).2).2
  let c : ℝ → ℂ := fun θ => ρ + (r : ℂ) * exp (Complex.I * (θ : ℂ))
  have hc : Continuous c := by fun_prop
  have hdist (θ : ℝ) : dist (c θ) ρ = r := by
    simp [c, dist_eq_norm, Complex.norm_exp, abs_of_pos hr]
  have hcn (θ : ℝ) : xi (c θ) ≠ 0 := by
    have hcR : c θ ∈ ball ρ R := by rw [mem_ball, hdist θ]; exact hrR
    rw [hfac _ hcR]
    apply mul_ne_zero _ (hu _ hcR)
    apply pow_ne_zero
    have hsub : c θ - ρ ≠ 0 := by
      change ρ + (r : ℂ) * exp (Complex.I * (θ : ℂ)) - ρ ≠ 0
      simpa using mul_ne_zero (show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne')
        (exp_ne_zero (Complex.I * (θ : ℂ)))
    exact hsub
  have hsource (θ : ℝ) : c θ ∈ psourceSet a F := by
    refine ⟨hcn θ, fun c' hc' hc0 => ?_⟩
    exact hball (y := c θ) (by rw [hdist θ]; exact hrε) c' (Finset.mem_filter.mpr ⟨hc', hc0⟩)
  have hclose : c 0 = c (2 * Real.pi) := by
    dsimp [c]
    rw [mul_zero, exp_zero]
    rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I by
      push_cast; ring, exp_two_pi_mul_I]
  let s : PSource a F := ⟨c 0, hsource 0⟩
  let p : Path s s :=
    { toFun := fun θ => ⟨c ((2 * Real.pi) * (θ : ℝ)), hsource _⟩
      continuous_toFun := (hc.comp
        (show Continuous (fun θ : unitInterval => (2 * Real.pi) * (θ : ℝ)) by fun_prop)).subtype_mk _
      source' := by apply Subtype.ext; simp [s]
      target' := by apply Subtype.ext; simpa [s] using hclose.symm }
  refine ⟨s, p, ?_⟩
  rw [normalizedWindingHom_mk]
  apply congrArg Multiplicative.ofAdd
  have hγ : IsLoop (fun θ => xi (c θ)) 0 (2 * Real.pi) :=
    ⟨xi_differentiable.continuous.comp hc, hcn, congrArg xi hclose⟩
  have he := bottcher_wind_eq_windingNumber
    (fun z : PSource a F => xi (z : ℂ))
    (xi_differentiable.continuous.comp continuous_subtype_val) (fun z => z.2.1) p hγ
    (fun θ => by simp only [zero_add, sub_zero]; rfl)
  change Bottcher.wind (fun z : PSource a F => xi (z : ℂ)) _ _ p = 1
  rw [he]
  simpa [c, ρ, ho] using hw r hr hrW

theorem pxi_winding_surjective :
    Function.Surjective (normalizedWindingHom (pxi a F) (pbase a F)) := by
  obtain ⟨s, p, hp⟩ := exists_plocal_winding_one a F
  exact normalizedWindingHom_surjective_of_one (pxi a F)
    (PathConnectedSpace.somePath s (pbase a F)) (FundamentalGroup.fromPath ⟦p⟧) hp

/-- **Every finite quotient receives the full monodromy image**, for every finite puncture set. -/
theorem finite_image_pmap {G : Type*} [Group G] [Finite G]
    (f : FundamentalGroup (PTarget F) (ptilt a F (pbase a F)) →* G) :
    (pmap a F).range.map f = f.range := by
  apply le_antisymm (Subgroup.map_le_range _ _)
  rintro _ ⟨q, rfl⟩
  obtain ⟨u, hu⟩ := pxi_winding_surjective a F (pwind F _ q)
  have hker : pwind F _ (q * (pmap a F u)⁻¹) = 1 := by
    rw [map_mul, map_inv, pwind_pmap, hu, mul_inv_cancel]
  have hn := finite_image_contains_kernel a F f _ hker
  have hm : f (pmap a F u) ∈ (pmap a F).range.map f := ⟨_, ⟨u, rfl⟩, rfl⟩
  have hprod := ((pmap a F).range.map f).mul_mem hn hm
  simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one] using hprod

/-! ## Connected pullbacks of finite coverings of `V_F` -/

variable {Y : Type*} [TopologicalSpace Y] {p : Y → PTarget F}

/-- The pullback `U_F ×_{V_F} Y` along `d_a`. -/
def ptiltPullback (p : Y → PTarget F) : Set (PSource a F × Y) := {q | ptilt a F q.1 = p q.2}

private theorem pjoined_to_base (hp : IsCoveringMap p) {q : PSource a F × Y}
    (hq : q ∈ ptiltPullback a F p) :
    ∃ e : p ⁻¹' {ptilt a F (pbase a F)},
      JoinedIn (ptiltPullback a F p) q (pbase a F, e.1) := by
  obtain ⟨u, y⟩ := q
  set sp := PathConnectedSpace.somePath u (pbase a F)
  set γ := sp.map (ptilt a F).continuous
  have h0 : γ 0 = p y := γ.source.trans hq
  set Γ := hp.liftPath γ.toContinuousMap y h0
  have hΓ : ∀ t, p (Γ t) = ptilt a F (sp t) := fun t => by
    have h1 : p (Γ t) = γ.toContinuousMap t :=
      congrFun (hp.liftPath_lifts γ.toContinuousMap y h0) t
    rw [h1]
    rfl
  have hfib : Γ 1 ∈ p ⁻¹' {ptilt a F (pbase a F)} := by
    change p (Γ 1) = _
    rw [hΓ 1, Path.target]
  have hΓ0 : Γ 0 = y := hp.liftPath_zero ..
  refine ⟨⟨Γ 1, hfib⟩, ?_⟩
  refine ⟨⟨⟨fun t => (sp t, Γ t), sp.continuous.prodMk Γ.continuous⟩, ?_, ?_⟩, fun t => ?_⟩
  · simp [hΓ0]
  · simp
  · exact (hΓ t).symm

private theorem pjoined_in_fiber (hp : IsCoveringMap p) [PathConnectedSpace Y]
    [Finite (p ⁻¹' {ptilt a F (pbase a F)})] (e e' : p ⁻¹' {ptilt a F (pbase a F)}) :
    JoinedIn (ptiltPullback a F p) (pbase a F, e.1) (pbase a F, e'.1) := by
  have he : p e.1 = ptilt a F (pbase a F) := e.2
  have he' : p e'.1 = ptilt a F (pbase a F) := e'.2
  set ρ := PathConnectedSpace.somePath e.1 e'.1
  set g : FundamentalGroup (PTarget F) (ptilt a F (pbase a F)) := FundamentalGroup.fromPath
    (((Path.Homotopic.Quotient.mk ρ).map ⟨p, hp.continuous⟩).cast he.symm he'.symm)
  have hg : hp.monodromy g e = e' := by
    apply hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk ρ)
    simp [g]
  set f := hp.monodromyPerm (ptilt a F (pbase a F))
  have hmem : f g ∈ (pmap a F).range.map f := by
    rw [finite_image_pmap]; exact ⟨g, rfl⟩
  obtain ⟨_, ⟨β, rfl⟩, hβ⟩ := hmem
  obtain ⟨b, rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath β)
  have hmono : hp.monodromy (pmap a F ⟦b⟧) e = e' := by
    have := congrArg (fun π : Equiv.Perm (p ⁻¹' {ptilt a F (pbase a F)}) => π e) hβ
    simpa [f, hg] using this
  set γ : Path (ptilt a F (pbase a F)) (ptilt a F (pbase a F)) :=
    (b.map (ptilt a F).continuous).cast rfl rfl
  have hsingle : pmap a F ⟦b⟧ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
    rw [pmap, FundamentalGroup.mapOfEq_apply]
    rfl
  have h0 : γ.toContinuousMap 0 = p e.1 := by rw [he]; exact γ.source
  set Γ := hp.liftPath γ.toContinuousMap e.1 h0
  have hΓ : ∀ t, p (Γ t) = ptilt a F (b t) := fun t => by
    have h1 : p (Γ t) = γ.toContinuousMap t :=
      congrFun (hp.liftPath_lifts γ.toContinuousMap e.1 h0) t
    rw [h1]
    rfl
  have hend : Γ 1 = e'.1 := by
    have := congrArg Subtype.val hmono
    rw [hsingle] at this
    exact this
  have hΓ0 : Γ 0 = e.1 := hp.liftPath_zero ..
  refine ⟨⟨⟨fun t => (b t, Γ t), b.continuous.prodMk Γ.continuous⟩, ?_, ?_⟩, fun t => ?_⟩
  · simp [hΓ0]
  · simp [hend]
  · exact (hΓ t).symm

/-- **Connected pullbacks.**  For every connected covering of `ℂ ∖ ({0} ∪ F)` with finite fibres,
the pullback along `d_a` is path connected. -/
theorem ptiltPullback_isPathConnected (hp : IsCoveringMap p) [ConnectedSpace Y]
    (hfin : ∀ x, Finite (p ⁻¹' {x})) : IsPathConnected (ptiltPullback a F p) := by
  haveI := locallyPathConnectedSpace_of_isCoveringMap hp
  haveI : PathConnectedSpace Y := PathConnectedSpace.of_locallyPathConnectedSpace
  haveI := hfin (ptilt a F (pbase a F))
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  set τ := PathConnectedSpace.somePath (p y) (ptilt a F (pbase a F))
  set Γ := hp.liftPath τ.toContinuousMap y τ.source
  have hfib : Γ 1 ∈ p ⁻¹' {ptilt a F (pbase a F)} := by
    change p (Γ 1) = _
    have := congrFun (hp.liftPath_lifts τ.toContinuousMap y τ.source) 1
    simpa using this
  set e₀ : p ⁻¹' {ptilt a F (pbase a F)} := ⟨Γ 1, hfib⟩
  have hbase : (pbase a F, e₀.1) ∈ ptiltPullback a F p := e₀.2.symm
  refine ⟨(pbase a F, e₀.1), hbase, fun {q} hq => ?_⟩
  obtain ⟨e, hqe⟩ := pjoined_to_base a F hp hq
  exact (pjoined_in_fiber a F hp e₀ e).trans hqe.symm

end

end RHTower.XiTiltMonodromy
