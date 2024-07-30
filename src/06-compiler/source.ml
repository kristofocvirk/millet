type ('a, 'b) phrase = {it : 'a; mutable et : 'b option}

let (@@) x = {it = x; et = None}


let it phrase = phrase.it
let et phrase = Option.get phrase.et

let map_it f phrase = {phrase with it = f phrase.it}
let map_et f phrase = {phrase with et = Option.map f phrase.et}

