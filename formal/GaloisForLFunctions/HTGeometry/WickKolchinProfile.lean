import GaloisForLFunctions.HTGeometry.AlgebraicMatroidRank
import GaloisForLFunctions.HTGeometry.DifferentialClockEmbeddingCovariance

/-!
# Finite Wick-reduced Kolchin profiles

For a family `connected sector jet`, this file separates the algebraic-transcendence rank already
visible in designated Gaussian sectors from the additional rank contributed by higher connected
sectors.  The construction is finite in both sector height and jet height.  It is an algebraic
profile, not yet a definition of a quantum field theory.

The key guardrail is exact: if every higher connected sector vanishes, the Wick-reduced rank is
zero even when the Gaussian packet itself has maximal jet rank.  The profile is also preserved by
injective base-field algebra maps, so it is not an artifact of an ambient field enlargement.
-/

open Set

namespace HTGeometry

open GaloisForLFunctions.MatroidGluing

noncomputable section

/-- Nonzero connected responses visible in a finite sector and jet window.  Zero is erased because
it is algebraic over every base field and carries no transcendence rank. -/
def connectedJetPacket
    {L ι : Type*} [Field L]
    (connected : ι → ℕ → L) (sectors : Finset ι) (jetHeight : ℕ) : Finset L := by
  classical
  exact ((sectors ×ˢ Finset.range (jetHeight + 1)).image
    (fun p ↦ connected p.1 p.2)).erase 0

theorem mem_connectedJetPacket_iff
    {L ι : Type*} [Field L]
    (connected : ι → ℕ → L) (sectors : Finset ι) (jetHeight : ℕ) (x : L) :
    x ∈ connectedJetPacket connected sectors jetHeight ↔
      x ≠ 0 ∧ ∃ i ∈ sectors, ∃ n < jetHeight + 1, connected i n = x := by
  classical
  constructor
  · intro hx
    rw [connectedJetPacket, Finset.mem_erase, Finset.mem_image] at hx
    obtain ⟨hx₀, p, hp, rfl⟩ := hx
    rw [Finset.mem_product, Finset.mem_range] at hp
    exact ⟨hx₀, p.1, hp.1, p.2, hp.2, rfl⟩
  · rintro ⟨hx₀, i, hi, n, hn, rfl⟩
    rw [connectedJetPacket, Finset.mem_erase, Finset.mem_image]
    exact ⟨hx₀, ⟨i, n⟩, by simp [hi, hn], rfl⟩

/-- Enlarging the connected-sector window enlarges the visible packet. -/
theorem connectedJetPacket_mono_sectors
    {L ι : Type*} [Field L]
    (connected : ι → ℕ → L) {small large : Finset ι}
    (h : small ⊆ large) (jetHeight : ℕ) :
    connectedJetPacket connected small jetHeight ⊆
      connectedJetPacket connected large jetHeight := by
  intro x hx
  rw [mem_connectedJetPacket_iff] at hx ⊢
  obtain ⟨hx₀, i, hi, n, hn, hix⟩ := hx
  exact ⟨hx₀, i, h hi, n, hn, hix⟩

/-- Enlarging the jet window enlarges the visible packet. -/
theorem connectedJetPacket_mono_jetHeight
    {L ι : Type*} [Field L]
    (connected : ι → ℕ → L) (sectors : Finset ι) {r s : ℕ}
    (h : r ≤ s) :
    connectedJetPacket connected sectors r ⊆
      connectedJetPacket connected sectors s := by
  intro x hx
  rw [mem_connectedJetPacket_iff] at hx ⊢
  obtain ⟨hx₀, i, hi, n, hn, hix⟩ := hx
  exact ⟨hx₀, i, hi, n, by omega, hix⟩

/-- Algebraic-transcendence rank of a finite packet.  Its implementation uses classical decidable
equality only to present the packet as a `Finset`. -/
noncomputable def finiteTranscendenceRank
    (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (packet : Finset L) : ℕ := by
  classical
  exact (transcendenceRank K L).ρ packet

/-- Algebraic-transcendence rank of a finite connected-sector jet packet. -/
noncomputable def finiteConnectedKolchinRank
    (K : Type*) {L ι : Type*} [Field K] [Field L] [Algebra K L]
    (connected : ι → ℕ → L) (sectors : Finset ι) (jetHeight : ℕ) : ℕ :=
  finiteTranscendenceRank K (connectedJetPacket connected sectors jetHeight)

/-- Relative finite rank contributed above the designated Gaussian connected sectors. -/
def finiteWickReducedKolchinRank
    (K : Type*) {L ι : Type*} [Field K] [Field L] [Algebra K L]
    (connected : ι → ℕ → L)
    (gaussian all : Finset ι) (jetHeight : ℕ) : ℕ :=
  finiteConnectedKolchinRank K connected all jetHeight -
    finiteConnectedKolchinRank K connected gaussian jetHeight

/-- The Gaussian packet rank is bounded by the full connected packet rank. -/
theorem finiteConnectedKolchinRank_mono_sectors
    (K : Type*) {L ι : Type*} [Field K] [Field L] [Algebra K L]
    (connected : ι → ℕ → L) {small large : Finset ι}
    (h : small ⊆ large) (jetHeight : ℕ) :
    finiteConnectedKolchinRank K connected small jetHeight ≤
      finiteConnectedKolchinRank K connected large jetHeight := by
  classical
  exact (transcendenceRank K L).mono
    (connectedJetPacket_mono_sectors connected h jetHeight)

/-- Rank decomposition into the Gaussian contribution and its Wick-reduced excess. -/
theorem finiteConnectedKolchinRank_gaussian_add_wickReduced
    (K : Type*) {L ι : Type*} [Field K] [Field L] [Algebra K L]
    (connected : ι → ℕ → L)
    {gaussian all : Finset ι} (h : gaussian ⊆ all) (jetHeight : ℕ) :
    finiteConnectedKolchinRank K connected gaussian jetHeight +
        finiteWickReducedKolchinRank K connected gaussian all jetHeight =
      finiteConnectedKolchinRank K connected all jetHeight := by
  have hle := finiteConnectedKolchinRank_mono_sectors
    K connected h jetHeight
  exact Nat.add_sub_of_le hle

/-- If every sector outside the Gaussian family vanishes, erasing the algebraic zero leaves
exactly the Gaussian connected packet. -/
theorem connectedJetPacket_eq_of_vanishes_off_gaussian
    {L ι : Type*} [Field L]
    (connected : ι → ℕ → L)
    {gaussian all : Finset ι} (hsub : gaussian ⊆ all)
    (hvanish : ∀ i ∈ all, i ∉ gaussian → ∀ n, connected i n = 0)
    (jetHeight : ℕ) :
    connectedJetPacket connected all jetHeight =
      connectedJetPacket connected gaussian jetHeight := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [mem_connectedJetPacket_iff] at hx ⊢
    obtain ⟨hx₀, i, hi, n, hn, hix⟩ := hx
    by_cases hig : i ∈ gaussian
    · exact ⟨hx₀, i, hig, n, hn, hix⟩
    · have hz := hvanish i hi hig n
      exfalso
      apply hx₀
      rw [← hix, hz]
  · exact connectedJetPacket_mono_sectors connected hsub jetHeight

/-- **Gaussian negative control.**  Vanishing of all higher connected sectors makes the finite
Wick-reduced Kolchin profile identically zero, independently of the two-point jet rank. -/
theorem finiteWickReducedKolchinRank_eq_zero_of_vanishes_off_gaussian
    (K : Type*) {L ι : Type*} [Field K] [Field L] [Algebra K L]
    (connected : ι → ℕ → L)
    {gaussian all : Finset ι} (hsub : gaussian ⊆ all)
    (hvanish : ∀ i ∈ all, i ∉ gaussian → ∀ n, connected i n = 0)
    (jetHeight : ℕ) :
    finiteWickReducedKolchinRank K connected gaussian all jetHeight = 0 := by
  rw [finiteWickReducedKolchinRank, finiteConnectedKolchinRank,
    finiteConnectedKolchinRank,
    connectedJetPacket_eq_of_vanishes_off_gaussian connected hsub hvanish]
  exact Nat.sub_self _

/-- Image of a finite packet under a base-field algebra map.  The classical decidable equality
needed by `Finset.image` is kept behind this noncomputable definition. -/
noncomputable def algHomImage
    (K : Type*) {L E : Type*}
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (e : L →ₐ[K] E) (s : Finset L) : Finset E := by
  classical
  exact s.image e

/-- Injective base-field algebra maps preserve the transcendence rank of every finite packet. -/
theorem transcendenceRank_image_algHom
    (K : Type*) {L E : Type*}
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (e : L →ₐ[K] E) (s : Finset L) :
    finiteTranscendenceRank K (algHomImage K e s) =
      finiteTranscendenceRank K s := by
  classical
  let ML := AlgebraicIndependent.matroid K L
  let ME := AlgebraicIndependent.matroid K E
  have hcomap : ME.comap e = ML := by
    apply Matroid.ext_indep
    · simp [ME, ML]
    · intro I hI
      rw [Matroid.comap_indep_iff]
      have hinj : Set.InjOn e I := e.injective.injOn
      rw [and_iff_left hinj]
      change AlgebraicIndepOn K id (e '' I) ↔ AlgebraicIndepOn K id I
      have himage := algebraicIndependent_image (R := K) hinj
      have hmap := AlgHom.algebraicIndependent_iff
        (x := fun x : I ↦ (x : L)) e e.injective
      simpa [AlgebraicIndepOn, Function.comp_def] using himage.symm.trans hmap
  have hrank := ME.eRk_comap (f := e) (↑s : Set L)
  rw [hcomap] at hrank
  have himage : e '' (↑s : Set L) = (↑(algHomImage K e s) : Set E) := by
    ext x
    simp [algHomImage]
  rw [himage] at hrank
  change (ME.eRk (↑(algHomImage K e s) : Set E)).toNat =
    (ML.eRk (↑s : Set L)).toNat
  exact congrArg ENat.toNat hrank.symm

/-- Mapping every connected jet through an injective base-field algebra map maps the whole finite
packet exactly. -/
theorem connectedJetPacket_map_algHom
    (K : Type*) {L E ι : Type*}
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (e : L →ₐ[K] E) (connected : ι → ℕ → L)
    (sectors : Finset ι) (jetHeight : ℕ) :
    connectedJetPacket (fun i n ↦ e (connected i n)) sectors jetHeight =
      algHomImage K e (connectedJetPacket connected sectors jetHeight) := by
  classical
  ext y
  constructor
  · intro hy
    rw [mem_connectedJetPacket_iff] at hy
    obtain ⟨hy₀, i, hi, n, hn, hiy⟩ := hy
    rw [algHomImage, Finset.mem_image]
    refine ⟨connected i n, ?_, hiy⟩
    rw [mem_connectedJetPacket_iff]
    refine ⟨?_, i, hi, n, hn, rfl⟩
    intro hz
    apply hy₀
    rw [hz, map_zero] at hiy
    exact hiy.symm
  · intro hy
    rw [algHomImage, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_connectedJetPacket_iff] at hx ⊢
    obtain ⟨hx₀, i, hi, n, hn, hix⟩ := hx
    refine ⟨(map_ne_zero e).2 hx₀, i, hi, n, hn, ?_⟩
    exact congrArg e hix

/-- Finite connected-sector Kolchin rank is invariant under injective ambient field embeddings. -/
theorem finiteConnectedKolchinRank_map_algHom
    (K : Type*) {L E ι : Type*}
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (e : L →ₐ[K] E) (connected : ι → ℕ → L)
    (sectors : Finset ι) (jetHeight : ℕ) :
    finiteConnectedKolchinRank K (fun i n ↦ e (connected i n)) sectors jetHeight =
      finiteConnectedKolchinRank K connected sectors jetHeight := by
  rw [finiteConnectedKolchinRank, connectedJetPacket_map_algHom K e connected]
  exact transcendenceRank_image_algHom K e _

/-- The Wick-reduced finite profile is invariant under injective ambient field embeddings. -/
theorem finiteWickReducedKolchinRank_map_algHom
    (K : Type*) {L E ι : Type*}
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (e : L →ₐ[K] E) (connected : ι → ℕ → L)
    (gaussian all : Finset ι) (jetHeight : ℕ) :
    finiteWickReducedKolchinRank K (fun i n ↦ e (connected i n))
        gaussian all jetHeight =
      finiteWickReducedKolchinRank K connected gaussian all jetHeight := by
  simp only [finiteWickReducedKolchinRank,
    finiteConnectedKolchinRank_map_algHom K e connected]

section DifferentialProfile

open scoped Differential

/-- Finite packet of actual differential jets of connected-sector responses. -/
def connectedDifferentialJetPacket
    {L ι : Type*} [Field L] [Differential L]
    (connected : ι → L) (sectors : Finset ι) (jetHeight : ℕ) : Finset L :=
  connectedJetPacket
    (fun i n ↦ GaloisForLFunctions.differentialJet n (connected i))
    sectors jetHeight

/-- Finite algebraic-transcendence rank of genuine differential jets. -/
noncomputable def finiteConnectedDifferentialKolchinRank
    (K : Type*) {L ι : Type*}
    [Field K] [Field L] [Algebra K L] [Differential L]
    (connected : ι → L) (sectors : Finset ι) (jetHeight : ℕ) : ℕ :=
  finiteConnectedKolchinRank K
    (fun i n ↦ GaloisForLFunctions.differentialJet n (connected i))
    sectors jetHeight

/-- Finite Wick-reduced rank formed from genuine differential jets. -/
noncomputable def finiteWickReducedDifferentialKolchinRank
    (K : Type*) {L ι : Type*}
    [Field K] [Field L] [Algebra K L] [Differential L]
    (connected : ι → L) (gaussian all : Finset ι) (jetHeight : ℕ) : ℕ :=
  finiteWickReducedKolchinRank K
    (fun i n ↦ GaloisForLFunctions.differentialJet n (connected i))
    gaussian all jetHeight

/-- A differential embedding maps the source differential-jet packet exactly onto the target
packet at the same sector and jet resolution. -/
theorem connectedDifferentialJetPacket_map_algHom
    (K : Type*) {L E ι : Type*}
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [Differential L] [Differential E]
    (e : L →ₐ[K] E) (hderiv : ∀ z : L, e z′ = (e z)′)
    (connected : ι → L) (sectors : Finset ι) (jetHeight : ℕ) :
    connectedDifferentialJetPacket (fun i ↦ e (connected i)) sectors jetHeight =
      algHomImage K e (connectedDifferentialJetPacket connected sectors jetHeight) := by
  unfold connectedDifferentialJetPacket
  have hfun :
      (fun i n ↦ GaloisForLFunctions.differentialJet n (e (connected i))) =
        (fun i n ↦ e (GaloisForLFunctions.differentialJet n (connected i))) := by
    funext i n
    exact (GaloisForLFunctions.HTGeometry.differentialJet_algHom
      e hderiv (connected i) n).symm
  rw [hfun]
  exact connectedJetPacket_map_algHom K e _ sectors jetHeight

/-- Finite differential connected-sector rank is invariant under derivation-preserving field
embeddings. -/
theorem finiteConnectedDifferentialKolchinRank_map_algHom
    (K : Type*) {L E ι : Type*}
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [Differential L] [Differential E]
    (e : L →ₐ[K] E) (hderiv : ∀ z : L, e z′ = (e z)′)
    (connected : ι → L) (sectors : Finset ι) (jetHeight : ℕ) :
    finiteConnectedDifferentialKolchinRank K (fun i ↦ e (connected i))
        sectors jetHeight =
      finiteConnectedDifferentialKolchinRank K connected sectors jetHeight := by
  unfold finiteConnectedDifferentialKolchinRank
  have hfun :
      (fun i n ↦ GaloisForLFunctions.differentialJet n (e (connected i))) =
        (fun i n ↦ e (GaloisForLFunctions.differentialJet n (connected i))) := by
    funext i n
    exact (GaloisForLFunctions.HTGeometry.differentialJet_algHom
      e hderiv (connected i) n).symm
  rw [hfun]
  exact finiteConnectedKolchinRank_map_algHom K e _ sectors jetHeight

/-- The finite Wick-reduced differential profile is invariant under every derivation-preserving
field embedding.  This is the finite source-frame covariance required by the proposed invariant. -/
theorem finiteWickReducedDifferentialKolchinRank_map_algHom
    (K : Type*) {L E ι : Type*}
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [Differential L] [Differential E]
    (e : L →ₐ[K] E) (hderiv : ∀ z : L, e z′ = (e z)′)
    (connected : ι → L) (gaussian all : Finset ι) (jetHeight : ℕ) :
    finiteWickReducedDifferentialKolchinRank K (fun i ↦ e (connected i))
        gaussian all jetHeight =
      finiteWickReducedDifferentialKolchinRank K connected gaussian all jetHeight := by
  unfold finiteWickReducedDifferentialKolchinRank
  have hfun :
      (fun i n ↦ GaloisForLFunctions.differentialJet n (e (connected i))) =
        (fun i n ↦ e (GaloisForLFunctions.differentialJet n (connected i))) := by
    funext i n
    exact (GaloisForLFunctions.HTGeometry.differentialJet_algHom
      e hderiv (connected i) n).symm
  rw [hfun]
  exact finiteWickReducedKolchinRank_map_algHom K e _ gaussian all jetHeight

/-- **Differential Gaussian negative control.**  If every connected response outside the
Gaussian sector is zero, the finite Wick-reduced differential profile vanishes at every jet
height. -/
theorem finiteWickReducedDifferentialKolchinRank_eq_zero_of_vanishes_off_gaussian
    (K : Type*) {L ι : Type*}
    [Field K] [Field L] [Algebra K L] [Differential L]
    (connected : ι → L) {gaussian all : Finset ι} (hsub : gaussian ⊆ all)
    (hvanish : ∀ i ∈ all, i ∉ gaussian → connected i = 0)
    (jetHeight : ℕ) :
    finiteWickReducedDifferentialKolchinRank K connected gaussian all jetHeight = 0 := by
  apply finiteWickReducedKolchinRank_eq_zero_of_vanishes_off_gaussian
    K (fun i n ↦ GaloisForLFunctions.differentialJet n (connected i)) hsub
  intro i hi hig n
  rw [hvanish i hi hig]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih]
      exact map_zero Differential.deriv

end DifferentialProfile

end

end HTGeometry
