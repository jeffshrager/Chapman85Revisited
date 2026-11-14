import Tweak.Extended.Conditional

/-!
# Synergy: why the criterion fails when effects depend on the input situation

Chapman (1985), §3.2.1, pp. 21–22 (the example is credited to David McAllester).

A block `d` has room for two blocks; `puton` needs room and uses one unit of it. Three
unordered steps `puton a d`, `puton b d`, `puton c d` start from room for two. Is "there is
room on `d`" true in the input situation of `puton a d`? "According to the modal truth
criterion, it is achieved so long as there is a situation t … necessarily before s in which p
is necessarily asserted … and that there is not even possibly a step between t and s that
denies p. … Does one deny p? No, because in t there is space for two, and each step only
decrements the space by one. Yet the two steps act synergistically to clobber p." (p. 22)

Room is encoded by three propositions `room 2`, `room 1`, `room 0`, exactly one true. "There is
room" is `¬(room 0)`. A `puton` moves the count down one if it can.

* `no_single_denier`: from the establishing (initial) situation, no step denies "there is
  room". This is the clobberer test as the paper applies it.
* `second_denies`: but a step run after another one does deny it. Denial has become a
  property of a step *in a situation*, not of the step, so a clobberer cannot be found by
  looking at steps one at a time: whether `C` clobbers depends on which other steps precede it.
* `synergy`: in the completion `puton b d`, `puton c d`, `puton a d`, there is no room before
  `puton a d`, so it is not necessarily true.
-/

namespace Tweak.Extended.Synergy

open Tweak.Ground Tweak.Extended

inductive Room | r0 | r1 | r2
  deriving DecidableEq

/-- The three `puton … d` steps (0 = `a`, 1 = `b`, 2 = `c`): each uses one unit of room if
there is any. -/
def eff : Fin 3 → List (Lit Room) → List (Lit Room) := fun _ st =>
  if (⟨.r2, true⟩ : Lit Room) ∈ st then [⟨.r1, true⟩, ⟨.r2, false⟩]
  else if (⟨.r1, true⟩ : Lit Room) ∈ st then [⟨.r0, true⟩, ⟨.r1, false⟩]
  else []

/-- Room for two on `d`. -/
def init : List (Lit Room) := [⟨.r2, true⟩, ⟨.r1, false⟩, ⟨.r0, false⟩]

/-- "There is room on `d`." -/
def room : Lit Room := ⟨.r0, false⟩

/-- The three steps are unordered. -/
def order : PPlan Room (Fin 3) where
  init := init
  step := fun _ => ⟨[], []⟩
  before := fun _ _ => false
  irrefl := by decide
  trans := by decide

/-- **No single step clobbers** (p. 22): "there is room" holds initially, and no step denies
it from there. -/
theorem no_single_denier : room ∈ init ∧ ∀ x, room.neg ∉ eff x init := by
  decide

/-- **A step denies it after another step**: each step denies "there is room" in the situation
any other step leaves. -/
theorem second_denies : ∀ x y, room.neg ∈ eff x (xrun eff init [y]) := by
  decide

/-- **Synergy** (p. 22): in the completion `b, c, a` there is no room before `puton a d`, so
"there is room" is not necessarily true there, although no single step clobbers it. -/
theorem synergy :
    ∃ L l₁ l₂, Completion order L ∧ L = l₁ ++ 0 :: l₂ ∧ room ∉ xrun eff init l₁ := by
  refine ⟨[1, 2, 0], [1, 2], [], ⟨by decide, by decide, by decide⟩, rfl, by decide⟩

end Tweak.Extended.Synergy
