module type S = sig
  include Backend.S

  val view_run_state : run_state -> bool -> unit
end
